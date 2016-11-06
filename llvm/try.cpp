#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <memory>
#include <string>
#include <vector>

using namespace llvm;

//=====-------------------------------------------------------------------------
// Lexer
//=====-------------------------------------------------------------------------

enum Token{
	tok_eof = -1,

	tok_def = -2,
	tok_extern = -3,

	tok_identifer = -4,
	tok_number = -5
};

static std::string IdentifierStr;	 // holds the name of the current identifier
static double NumVal;	// holds the current value


static int gottok(){
	static int LastChar = ' ';

	while(isspace(LastChar))
		LastChar = getchar();

	if(isalpha(LastChar)){		// keyword & identifier
		IdentifierStr = LastChar;
		while (isalnum(LastChar = getchar()))
			IdentifierStr += LastChar;
		if(IdentifierStr == "def")
			return tok_def;
		if(IdentifierStr == "extern")
			return tok_extern;
		return tok_identifer;
	}

	if(isdigit(LastChar)||LastChar == '.'){	// float number
		std::string NumStr;

		do {
			NumStr += LastChar;
			LastChar = getchar();
		} while(isdigit(LastChar)||LastChar == '.');
		NumVal = strtod(NumStr.c_str(), nullptr);
		return tok_number;
	}

	if(LastChar == '#'){	// one line comment
		LastChar = getchar();
		while (LastChar != EOF && LastChar != '\n' && LastChar != '\r') {
			LastChar = getchar();
		}

		if(LastChar != EOF){
			return gottok();
		}
	}

	if(LastChar == EOF)	// handel EOF
		return tok_eof;

	int ThisChar = LastChar;	// handle operator: +,-,...
	LastChar = getchar();	// ???
	return ThisChar;
}






//=====-------------------------------------------------------------------------
// AST
//=====-------------------------------------------------------------------------
namespace {

class ExprAst{

public:
	virtual ~ExprAst(){}
};


// number
class NumberExprAst : public ExprAst{
	double Val;
public:
	NumberExprAst(double v): Val(v){}
};


//variable
class VariableExprAst : public ExprAst{
	std::string name;
public:
	VariableExprAst(const std::string &Name):name(Name){}
};


// binary operation
class BinOpExprAst : public ExprAst{
	char op;
	std::unique_ptr<ExprAst> Lexpr, Rexpr;
public:
	BinOpExprAst(char Op, std::unique_ptr<ExprAst> L,
		std::unique_ptr<ExprAst> R):
		op(Op), Lexpr(std::move(L)), Rexpr(std::move(R)){}
};



// call expression
class CallExprAst: public ExprAst{
	std::string callee;
	std::vector<std::unique_ptr<ExprAst>> args;
public:
	CallExprAst(const std::string & Callee,
				std::vector<std::unique_ptr<ExprAst>> Args):
				callee(Callee), args(std::move(Args)){}
};




// function ast prototype
class PrototypeAst: public ExprAst{
	std::string name;
	std::vector<std::string> args;
public:
	PrototypeAst(const std::string &Name,
				 std::vector<std::string> Args)
				 : name(Name), args(std::move(Args)){}
};

class FunctionAst: public ExprAst{
	std::unique_ptr<PrototypeAst> proto;
	std::unique_ptr<ExprAst> body;
public:
	FunctionAst(std::unique_ptr<PrototypeAst> Proto,
				std::unique_ptr<ExprAst> Body)
				: proto(std::move(Proto)), body(std::move(Body)) {}
};

}// end of namespace


//=====-------------------------------------------------------------------------
// parser
//=====-------------------------------------------------------------------------

//basic
static int CurTok;
static int getNextToken(){
	return CurTok = gottok();
}

// error handing
std::unique_ptr<ExprAst> LogError(const char *Str){
	fprintf(stderr, "LogError %s\n", Str);
	return nullptr;
}

std::unique_ptr<PrototypeAst> LogErrorP(const char *Str){
	LogError(Str);
	return nullptr;
}




// number
std::unique_ptr<ExprAst> ParseNumberExpr(){
	auto result = llvm::make_unique<NumberExprAst>(NumVal);
	getNextToken();
	return std::move(result);
}

//paren expression
static std::unique_ptr<ExprAst> ParseExpression();

std::unique_ptr<ExprAst> ParseParenExpr(){
	getNextToken(); //eat '('
	auto v = ParseExpression();
	if(!v)
		return nullptr;

	if(CurTok != ')') // (4 3):error  (4):right
		return LogError("expected ')'");
	getNextToken(); // eat ')'
	return v;
}

// identifierexpr
//   ::= identifier
//   ::= identifier '(' expression* ')'
static std::unique_ptr<ExprAst> ParseIdentifierExpr(){
	std::string IdName = IdentifierStr;

	getNextToken();
	if(CurTok != '(')
		return llvm::make_unique<VariableExprAst>(IdName); //handle variable


	//handle call
	getNextToken();// eat '('
	std::vector<std::unique_ptr<ExprAst>> args;
	if(CurTok != ')'){
		while (true) {
			if(auto exp = ParseExpression())
				args.push_back(std::move(exp));
			else
				return nullptr;

			if(CurTok == ')')
				break;

			if(CurTok != ',')
				return LogError("Expected ',' or ')' in argument list");

			getNextToken();//eat ','
		}
	}
	getNextToken();//eat ')'
	return llvm::make_unique<CallExprAst>(IdName, std::move(args));
}

/// primary
///   ::= identifierexpr
///   ::= numberexpr
///   ::= parenexpr
static std::unique_ptr<ExprAst> ParsePrimary(){
	switch (CurTok) {
		case tok_identifer:
			return ParseIdentifierExpr();
		case tok_number:
			return ParseNumberExpr();
		case '(':
			return ParseParenExpr();
		default:
			return LogError("unknown token when expecting an expression");
	}
}



//
static std::map<char, int> BinopPrecedence;

static int GetTokPrecedence(){
	if(!isascii(CurTok)){
		return -1;
	}
	int tokPrec = BinopPrecedence[CurTok];
	if(tokPrec <= 0) return  -1;
	return tokPrec;
}

/// expression
///   ::= primary binoprhs
static std::unique_ptr<ExprAst> ParseBinOpRHS(int ExprPrec, std::unique_ptr<ExprAst> LHS);

static std::unique_ptr<ExprAst> ParseExpression(){
	auto LHS = ParsePrimary();
	if(!LHS)
		return nullptr;
	return ParseBinOpRHS(0, std::move(LHS));
}

static std::unique_ptr<ExprAst> ParseBinOpRHS(int ExprPrec, std::unique_ptr<ExprAst> LHS){
	while(true){
		int tokPrec = GetTokPrecedence();
		if(tokPrec < ExprPrec)
			return LHS;

		int BinOP = CurTok;
		getNextToken();

		auto RHS = ParsePrimary();
		if(!RHS)
			return nullptr;

		int nextPrec = GetTokPrecedence();
		if(tokPrec < nextPrec){
			RHS = ParseBinOpRHS(tokPrec + 1, std::move(RHS));
			if(!RHS)
				return nullptr;
		}
	LHS = llvm::make_unique<BinOpExprAst>(BinOP, std::move(LHS), std::move(RHS));
	}
}



// function

/// prototype
///   ::= id '(' id* ')' //eg: def f(x y z) x+y+z
static std::unique_ptr<PrototypeAst> ParsePrototype(){
	if(CurTok != tok_identifer)
		return LogErrorP("Expected function name in prototype");

	std::string FunName = IdentifierStr;

	getNextToken();
	if(CurTok != '(')
		return LogErrorP("Expected '(' in prototype");

	// Read the list of argument names.
	std::vector<std::string> argNames;
	while (getNextToken() == tok_identifer) {
		argNames.push_back(IdentifierStr);
	}
	if(CurTok != ')')
		return LogErrorP("Expected ')' in prototype");

	getNextToken(); //eat ')'
	return llvm::make_unique<PrototypeAst>(FunName, std::move(argNames));
}

/// definition ::= 'def' prototype expression
static std::unique_ptr<FunctionAst> ParseDefinition(){
	getNextToken(); //eat 'def'
	auto Proto = ParsePrototype();
	if(!Proto)
		return nullptr;

	if (auto E = ParseExpression())
      return llvm::make_unique<FunctionAst>(std::move(Proto), std::move(E));
    return nullptr;
}

/// external ::= 'extern' prototype
static std::unique_ptr<PrototypeAst> ParseExtern(){
	getNextToken();//eat 'extern'
	return ParsePrototype();
}

/// toplevelexpr ::= expression
static std::unique_ptr<FunctionAst> ParseTopLevelExpr(){
	if(auto E = ParseExpression()){
		auto Proto = llvm::make_unique<PrototypeAst>("", std::vector<std::string>());
		return llvm::make_unique<FunctionAst>(std::move(Proto), std::move(E));
	}
	return nullptr;
}



// river
/// top ::= definition | external | expression | ';'

static void HandleDefinition(){
	if (ParseDefinition()) {
    	fprintf(stderr, "Parsed a function definition.\n");
  	} else {
    	// Skip token for error recovery.
    	getNextToken();
  	}
}

static void HandleExtern(){
	if (ParseExtern()) {
      fprintf(stderr, "Parsed an extern\n");
    } else {
      // Skip token for error recovery.
      getNextToken();
    }
}

static void HandleTopLevelExpression(){
	// Evaluate a top-level expression into an anonymous function.
    if (ParseTopLevelExpr()) {
      fprintf(stderr, "Parsed a top-level expr\n");
    } else {
      // Skip token for error recovery.
      getNextToken();
    }
}

static void MainLoop(){
	while (true) {
		fprintf(stderr, "ready> ");
		switch (CurTok) {
			case tok_eof:
				return;
			case ';':
				getNextToken();
				break;
			case tok_def:
				HandleDefinition();
				break;
			case tok_extern:
				HandleExtern();
				break;
			default:
				HandleTopLevelExpression();
				break;
		}
	}
}





int main() {
	BinopPrecedence['<'] = 10;
	BinopPrecedence['+'] = 20;
	BinopPrecedence['-'] = 20;
	BinopPrecedence['*'] = 40;
	// Prime the first token.
	fprintf(stderr, "ready> ");
	getNextToken();

	// Run the main "interpreter loop" now.
	MainLoop();

	return 0;
}

// compile:
// clang++ -g -O3 try.cpp `llvm-config --cxxflags --ldflags --system-libs --libs core` -o try
