						Code Library
						 Wang Lulu
						 July, 2015
_________________________________________________________________
=================================================================
>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
.................................................................
_________________________________________________________________
_________________________________________________________________



							Contents
_________________________________________________________________

经验与技巧
A.
B.
C.

常用STL
A: 定义自己的类型
B: vector
C: stack
D: queue
E: priority_queue
F: set/multiset
G: map/multimap
H: algorithm


结构及操作
A 
B 
C 


通用算法
A 
B
C


数学方法
A 
B 
C


特化问题及其算法
A 
B 
C 





_________________________________________________________________
=================================================================
_________________________________________________________________


经验与技巧
_________________________________________________________________

	1.int数组快速初始化：

		#include<string.h>		//注意这里是string.h
		int m[100][200];
		memset(m,-1,sizeof(m));	//将m全初始化为-1
		memset(m,0,sizeof(m));	//将m全初始化为0

    2. 用struct或class封装时,不能开辟过大的空间,否则会运行时错误，
       若要开辟大空间(大数组),应开辟全局变量，并使用c语言的方式，不要
       用struct或class封装。


常用STL
_________________________________________________________________

A: 自己定义类型
_________________________________________________________________

struct Type{
	int a;
	bool b;
	char c;
	...
	//------------------------
	Type(){	//构造函数(可选)
		a = xx;
		b = xx;
		...
	}
	Type(int _a, bool _b){	//带参构造函数(可选)
		a = _a;
		b = _b;
		...
	}
	//----------------------
	/*使Type具有判等性(可选)*/
	friend bool operator==(Type x,Type y){
		//自己定义相等的概念
        if(x.a==y.a&&x.b==y.b&&x.c==y.c&&...)	
            return true;
        else
            return false;
    	}
	
	/*使Type自身具有可比性(可以比较大小)(可选)*/
	friend bool operator<(Type x,Type y){
		//自己定义<的概念，如果返回TRUE认为x<y,
		//否则认为x>=y
		//eg. return x.a<y.a && x.c<y.c; 
	}
};

_________________________________________________________________

B: vector
_________________________________________________________________

1.vector中的元素在内存中是顺序排列的，对查找的开销小，对插入的开销大，
  但在尾部插入仍是O(1)。
2.vector没有越界检查，要自己控制以防越界。
3.vector开销大，尽量用数组代替它


#include<vector>	//header

vector<Type> v;		//declear
v.assign(size,value);			//用size个value初始化v
v.assign(first_iter,last_iter);	//用两个iterator之间的元素初始化v
								//左闭右开：[first_iter last_lter)
v.clear();				//清空v中的元素
v.empty();				//v为空返回true否则返回false
v.push_back(e);			//push e to the back of v
v[index];				//read or write v use index
v.insert(iter,e);		//把e插入iter所处位置，iter和之后的元素后移
v.front();				//return the first obj of v
v.back();				//return the last obj of v
v.size();				//返回v中的元素数

v.begin();			//return the iterator of the first obj
v.end();			//return the iterator after the last obj
					//左必右开：[v.begin v.end)

ADD: 迭代器iterator的用法：
_________________________________________________________________

1.iterator是指针的扩充，用法和指针很相似。创建方式如下：
	容器类型<元素类型>::iterator 名称；
eg: 	
	set<int>::iterator iter;
	vector<char>::iterator aaa;
2.支持的操作如下：
	访问内容：			*(iterater)
	移向下一个元素：		iterater++/++iterater
	求两迭代器之间的元素数：	last_iter - first_lter
    
    *注意：迭代器不支持加减运算，这一点与指针不同。迭代器的++/--操作对线性容器
	 和关联容器都适用。

B: stack
_________________________________________________________________

#include<stack>	//header

stack<Type> s;	//declear
s.push(e);		//push a obj
s.top();		//return the top of a stack
s.pop();		//pop a obj from the stack
s.size();		//return the size of the stack
s.empty();		//return true if the stack is empty(s.size=0),
				//false if not


C: queue
_________________________________________________________________

#include<queue>	//header

queue<Type> q;	//declear
q.push(e);		//push a obj
q.front();		//return the front ob of the queue
q.back();		//return the last obj of the queue
q.pop();		//pop the first obj of the queue
q.empty();		//return true if the stack is empty(s.size=0),
				//false if not

q.size();		//return the size of the queue



D: priority_queue
_________________________________________________________________

1.因为priority_queue涉及到排序，因此要为Type制定优先级比较方式，
  否则会按Type本身的值比较结构作为优先级。
2.priority_queue是大顶堆，即优先级最高的元素在最前面，
  通过制定不同的优先级比较方式可以得到该种优先级意义下的大顶堆。

#include<queue>	//header(the same with queue)

priority_queue<Type> q;	//declear(使用自身的值比较作为优先级,
						//灵活性很差[不推荐！])
priority_queue<Type,vector<Type>,my_prior> q; 
						//declear(使用my_prior提供的优先级
						//函数进行比较[推荐！])

q.push(e);			//push a obj
q.top();			//return the top obj of the heap
q.pop();			//pop the top obj of the heap
q.empty();			//return true if the size is 0
q.size();			//return the size 


ADD: 提供优先级的my_prior的写法：
_________________________________________________________________

1.注意my_prior实际上是结构体(与sort函数的情况不同)，和operator的特殊写法。

struct my_prior{
	bool operator()(Type x,Type y) const //注意"要加const!!!"
	{
		//返回TRUE认为x优先级低于y
		//否则认为x优先级>=y
	}
};


E: set/multiset
_________________________________________________________________

1.set与multiset本质是平衡搜索树，它是有序的，并且插入和查找时间都为log(n),
  解决了向量插入和列表查找时开销大的问题。
2.set的元素不能重复，multiset的元素可以重复。
3.set/multiset中的元素按优先级：左子树<根节点<右子树 的顺序构建，默认使用
  元素自身的比较方式作为优先级，可以自己指定优先级函数.
4.set只能通过iterator访问元素的值

#include<set>				//header

set<Type> s;				//同优先级队列，这里使用Type自己的比较方
							//式作为优先级。
set<Type,my_prior> s;		//使用my_prior提供的优先级函数进行比较。

multiset<Type> s;			//允许元素重复，其余同上
multiset<Type,my_prior> s;	//同上

s.insert(e);				//将e插入s中，set不保留重复的，
							//multiset会保留所有插入的元素
s.insert(first_iter,last_iter);
							//将[first_iter last_iter)内的所有指向
							//的元素插入s
s.find(e);					//返回一个iterator指向值为e的元素,
							//没有发现返回s.end()

s.erase(e);					//将值为e的元素删除。
s.erase(iter);				//将iter指向的元素删除
s.erase(iter_first,iter_last);	//将[first_iter last_iter)内
								//所有指向的元素删除

s.clear();						//清空s中的所有元素
s.empty();						//s为空返回true,否则返回false
s.size();						//返回s中元素个数
s.begin()/s.end();				//同前面几节
s.count(e);						//返回值为e的元素个数，这里只可能
								//为1或0，multiset中可以为大于1的数

s.lower_bound(e);				//返回一个iterator，指向第一个大于
								//等于e的元素(多用于multiset)
s.upper_bound(e);				//返回一个iterator，指向第一个大于
								//e的元素(多用于multiset)


F: map/multimap
_________________________________________________________________

1.map即字典，实现字典通常有两种方式：hash表与二叉搜索树，map使用的是二叉搜索树。
2.map可以看做每个元素都附加了一个属性值的set，即map中每一个元素都由key-value
  组成，如果忽略value只看key那么map和set几乎一样。
3.与set相同，map中key值相同的元素只能有一个，而multiset可以有多个。
4.map/multimap中元素的本质是一些pair，访问方式有两种：iterator和下标访问。
5.同优先级队列，map/multimap中的元素按key的优先级：左子树<根节点<右子树 的顺
  序构建，默认使用元素中key的自身的比较方式作为优先级，可以自己指定优先级函数

#include<map>		//header

map<Type_key,Type_val> m;			
					//同优先级队列，这里使用TypeA自己的比较方式作为优先级。
map<Type_key,Type_val,my_prior> m;	
					//使用my_prior为Type_key提供的优先级函数	进行比较。

multimap<Type_key,Type_val> m;			//允许元素重复，其余同上
multimap<Type_key,Type_val,my_prior> m;	//同上

m.insert(pair_e);				
		//将pair_e插入m中，map不保留重复的，而multimap会保留所有插入的元素

m.insert(first_iter,last_iter);	
		//将[first_iter last_iter)内的所有指向的元素(pair类型)插入m

m.find(key);					
		//返回一个iterator指向键值为key的元素，没有发现返回m.end()

m.erase(key);					//将键值为key的元素删除。
m.erase(iter);					//将iter指向的元素删除
m.erase(iter_first,iter_last);	
		//将[first_iter last_iter)内所有指向的元素删除

m.clear();				//清空m中的所有元素
m.empty();				//m为空返回true,否则返回false
m.size();				//返回m中元素个数
m.begin()/s.end();		//同前面几节
m.count(key);			
		//返回键值为key的元素个数,这里只可能为1或0,multimap中可以为大于1的数.

m.lower_bound(key);		
		//返回一个iterator，指向第一个键值大于等于key的元素(多用于multimap)
m.upper_bound(key);		
		//返回一个iterator，指向第一个键值大于key的元素(多用于multimap)

ADD:
_________________________________________________________________

1. map/multimap的iterator指向的是pair,不能像别的容器那样直接用*()访问其值,
   而是通过iter->first和iter->second来访问它的key与value.
2. map支持特有的下标访问方式，multimap不支持.
3. 下标访问map与下标访问vector截然不同,下标访问vector类似于访问数组，
   而下标访问map中不存在的元素将导致在map中添加一个新元素，其key就是访问它的
   那个下标,value为对应类型下的默认初始值，如int为0，string为空串.















结构及操作
_________________________________________________________________
_________________________________________________________________
A. 插入与查找：数组，链表，平衡树，hash表

				插入			查找
数组	(有序)		o(n)		o(lgn)
链表	(有序)		o(1)		o(n)
平衡树			o(lgn)		o(lgn)
hash表			o(1)		o(1)

1. 在对性能要求苛刻的情况下选择平衡树(set/map)或hash表,优先选择平衡树，
   平衡树依然超时的情况下才考虑hash表。
2. hash表的性能不稳定，严重依赖于hash函数的好坏，因此hash函数的选择要慎重。
3. 使用hash表时，优先考虑不会发生冲突的方法，如果内存过大再考虑可能发生冲突
   的方法。

hash模板：
接口：	void h_insert(Type e)
		int h_find(Type e)
1. e相同也分别存储的情况：

#define maxh 20003	
#define maxn 10005

short hash_t[maxh];
int value_t[maxn];
short next_t[maxn];
int ind;

void hinsert(int t)
{
    value_t[ind]=t;
    
    t=t<0?-t:t;
    int h = (t%maxh+t/maxh)%maxh;
    
    next_t[ind]=hash_t[h];
    hash_t[h]=ind++;
}

int hfind(int t)
{
	int count=0;
    int tt = t<0?-t:t;
    int h = (tt%maxh+tt/maxh)%maxh;
    int x = hash_t[h];
    while(x){
        if(value_t[x]==t)
            count++;
        x=next_t[x];
    }
    return count;
}

2. e相同只将其计数值加1

再创建一个数组
short count_t[maxn];	//用于记录value_t表中个元素出现的次数

然后再稍微改动一下hinsert和hfind函数就可以了。



B: 大数模板
_________________________________________________________________

补:主要是加法和乘法,除法和减法都可以由乘法和加法通过二分查询简单实现。

#include <vector>
#include <stdio.h>
#include <string.h>
#include <string>
#include <iostream>
using namespace std;

struct BigInt
{
    static const int BASE = 10000;
    static const int WIDTH = 4;
    vector<int> s;
    
    BigInt(){s.clear();}
    
    BigInt operator=(int t)
    {
        s.clear();
        while(t!=0)
        {
            s.push_back(t%BASE);
            t=t/BASE;
        }
        return *this;
    }
    
    BigInt operator=(const BigInt &bt)
    {
        s.clear();
        int l = bt.s.size();
        for(int i=0;i<l;i++)
            s.push_back(bt.s[i]);
        return *this;
    }
    
    BigInt operator=(const string &str)
    {
        s.clear();
        int mend = str.length();
        int mbegin = mend-WIDTH;    //注意
        int t;
        while(mbegin>0)
        {
            sscanf(str.substr(mbegin,mend-mbegin).c_str(),"%d",&t); //注意
            s.push_back(t);
            mend-=WIDTH;
            mbegin-=WIDTH;
        }
        sscanf(str.substr(0,mend).c_str(),"%d",&t);
        s.push_back(t);
        return *this;
    }
    
    BigInt operator+(const BigInt &bt)
    {
        int carry = 0;
        int i = 0;
        BigInt t;
        while(i<s.size()||i<bt.s.size()||carry>0)   //注意carry>0也满足条件
        {
            if(i<s.size())
                carry+=s[i];
            if(i<bt.s.size())
                carry+=bt.s[i];
            i++;
            t.s.push_back(carry%BASE);
            carry/=BASE;
        }
        return t;
    }
    
    BigInt operator-(const BigInt &bt)  //前面的数一定大于后面的数
    {
        int carry = 0;
        int i = 0;
        BigInt t = *this;
        BigInt ans;
        int x;
        while(i<t.s.size()||i<bt.s.size())
        {
            x = t.s[i]-carry;
            carry = 0;
            if(i<bt.s.size())
                x-=bt.s[i];
            if(x<0)
            {
                x+=BASE;
                carry++;
            }
            ans.s.push_back(x);
            i++;
        }
        while(ans.s[t.s.size()-1]==0) //注意消除高位产生的零
            ans.s.erase(ans.s.end()-1);
        return ans;
    }
    
    BigInt operator*(const BigInt &bt)  //记住乘法运算机制
    {
        int l = s.size()>bt.s.size()?s.size():bt.s.size();
        l*=2;   //注意乘2
        BigInt t;
        int x;
        int carry = 0;
        int i,j;
        for(i=0;i<l;i++)
        {
            x=carry;
            for(j=0;j<=i;j++)   //注意含义
            {
                if(j<s.size()&&(i-j)<bt.s.size())
                    x += s[j]*bt.s[i-j];
            }
            t.s.push_back(x%BASE);
            carry = x/BASE;
        }
        while(t.s.size()!=0&&t.s[t.s.size()-1]==0)  //注意消除高位产生的零
            t.s.erase(t.s.end()-1);
        return t;
    }
    /*
     BigInt operator/(BigInt bt)
     {
     
     }
     BigInt operator%(BigInt bt)
     {
     
     }
     */
    void print()
    {
        int i = s.size();
        int t;
        if(i==0)    //注意处理值为零(s为空)的情况
            printf("0");
        if(i>0) //注意最高位要消除前导零
            printf("%d",s[--i]);
        while(i>0)  //注意中间位要加上前导零
        {
            t=1000;
            int x = s[i-1];
            for(int j=WIDTH;j>0;j--)
            {
                printf("%d",x/t);
                x = x%t;
                t=t/10;
            }
            i--;
        }
    }
};



C: 网络流
_________________________________________________________________
1. SAP算法模板：BFS找增广路

#include <vector>
#include <stdio.h>
#include <string.h>
#include <string>
#include <queue>
#include <iostream>
using namespace std;

struct MaxFlaw{
    
    static const int NODE_CON = 210;
    static const int MAX_CAP = 10000000;
    
    int left[NODE_CON][NODE_CON];
    int pre[NODE_CON];
    bool vis[NODE_CON];
    int first,last;
    
    void init_range(int s,int e)
    {
        first=s;
        last=e;
        memset(left, 0, sizeof(left));
        memset(pre, -1, sizeof(pre));
        memset(vis, 0, sizeof(vis));
    }
    void add_edge(int s,int e, int cap)
    {
        left[s][e] += cap;      //注意可能有平行边所以用加法
    }
    
    int BFS(int s, int t)
    {
        memset(pre, -1, sizeof(pre));
        memset(vis, 0, sizeof(vis));
        
        queue<int> q;
        q.push(s);
        vis[s]=true;
        while(!q.empty())
        {
            int f = q.front();
            q.pop();
            for(int i = first;i<=last;i++)
            {
                if(vis[i]==false&&left[f][i]>0)
                {
                    pre[i]=f;
                    q.push(i);
                    vis[i]=true;
                    if(i==t)    //找到一条路径
                    {
                        while(!q.empty())
                            q.pop();
                        break;
                    }
                }
            }
        }
        if(pre[t]!=-1)
        {
            int min = MAX_CAP+1;
            int be = pre[t];
            int en = t;
            while(be!=-1)
            {
                if(left[be][en]<min)
                    min = left[be][en];
                en=be;
                be=pre[be];
            }
            be = pre[t];
            en = t;
            while(be!=-1)
            {
                left[be][en]-=min;
                left[en][be]+=min;
                en=be;
                be=pre[be];
            }
            return min;
        }else
            return 0;
    }
    
    int max_flaw(int source, int target)
    {
        int ans=0;
        int t;
        while((t=BFS(source,target)))
            ans+=t;
        return ans;
    }
};

2. Dinic算法：BFS分层+DFS按层找增广路
#include <vector>
#include <stdio.h>
#include <string.h>
#include <string>
#include <queue>
#include <iostream>
using namespace std;

struct MaxFlaw{
    
    static const int NODE_CON = 210;
    static const int MAX_CAP = 10000000;
    
    int left[NODE_CON][NODE_CON];
    int level[NODE_CON];
    int pre[NODE_CON];
    bool vis[NODE_CON];
    int first,last;
    
    void init_range(int s,int e)
    {
        first=s;
        last=e;
        memset(left, 0, sizeof(left));
        memset(pre, -1, sizeof(pre));
        memset(vis, 0, sizeof(vis));
        memset(level,0,sizeof(level));
    }
    void add_edge(int s,int e, int cap)
    {
        left[s][e] += cap;      //注意可能有平行边所以用加法
    }
    
    void BFS(int s, int t)
    {
        memset(pre, -1, sizeof(pre));
        memset(vis, 0, sizeof(vis));
        memset(level, 0, sizeof(level));
        
        queue<int> q;
        q.push(s);
        level[s]=1;
        vis[s]=true;
        while(!q.empty())
        {
            int f = q.front();
            q.pop();
            for(int i = first;i<=last;i++)
            {
                if(vis[i]==false&&left[f][i]>0)
                {
                    pre[i]=f;
                    q.push(i);
                    vis[i]=true;
                    level[i]=level[f]+1;
                }
            }
        }
    }
    
    int DFS(int s, int e,int mf)    //不需要用vis判重了,
    {                               //每次只选下一层不会重复
        if(s==e)return mf;
        for(int i=first;i<=last;i++)
        {
            if(left[s][i]>0&&level[i]>level[s])
            {
                int a = DFS(i, e, left[s][i]>mf?mf:left[s][i]);
                if(a>0)
                {
                    left[s][i]-=a;
                    left[i][s]+=a;
                    return a;
                }
            }
        }
        return 0;
    }
    
    int max_flaw(int source, int target)
    {
        int ans=0;
        while(1)
        {
            BFS(source,target);
            if(level[target]==0)
                return ans;
            int t;
            while((t=DFS(source,target,MAX_CAP)))
            {
                ans+=t;
            }
        }
        return ans;
    }
};


D:二分图匹配
_________________________________________________________________
D1:可以转化为网络流模型问题，可直接用网络流模板这里略过

D2:一个更简单地算法：匈牙利算法
   1.图的两部分统一编码，级n个对象与m个对象匹配时，范围为[1,n+m]
   2.最终调用max_match时，只需传入一个图的部分的范围即可，即参数可以为[1,n],
     或[n+1,n+m],不要传入[1,n+m],这样会出错。


static const int MAXN=1000; //这里的MAXN是二分图两部分节点数量和
vector<int> G[MAXN+10];
int match[MAXN+10];         //保存匹配的对象
bool asked[MAXN+10];        //dfs时使用，防止腾让对象时发生循环请求，
                            //导致无限递归

void init_G()
{
    memset(match, -1, sizeof(match));
    for(int i=0;i<=MAXN;i++)    //(如果有多个用例)这个不要忘了
        G[i].clear();
}

void ADD_edge(int s,int e)
{
    G[s].push_back(e);
    G[e].push_back(s);
}

bool dfs(int v)
{
    asked[v]=true;      //v可能为请求发出者之一，不参与其匹配过程中的腾让请求
    int next;
    for(int i=0;i<G[v].size();i++)
    {
        next = G[v][i];
        if(match[next]==-1) //如果还没有匹配,就匹配她
        {
            match[v]=next;
            match[next]=v;
            return true;
        }else   //如果已经被匹配,就请求她匹配的对象把她让给自己，如果她匹配的对象
        {       //还能找到新的对象就让出当前的对象，否则不让出
            int goodman = match[next];
            if(asked[goodman]==false&&dfs(goodman)==true) //递归，
            {                                     //为goodman寻找新的对象
                                        //第一个条件防止循环请求导致无限递归
                match[v]=next;
                match[next]=v;
                return true;
            }
        }
    }   //已经找完所有认识的对象，但都没有匹配成功，返回匹配失败
    return false;
}

int max_match(int s,int e)
{
    int ans=0;
    for(int i=s;i<=e;i++)   //为每一个节点找一次对象
    {
        memset(asked, 0, sizeof(asked));
        if(dfs(i))
            ans++;          //找到就成功匹配一个
    }
    return ans;
}



E: 线段树(区间树)
_________________________________________________________________

1. 用于查询区间信息，如最大，最小值，区间和等，但这种信息必须是
   可以递推的，即知道子区间的信息就能直接计算出父区间的信息。
2. 接口有build,update和query,用于改,查操作.而不支持增删.
3. 线段树的区间可以不从0或1开始,可以自定义开始点和结束点。
4. 根据这里的寻找左右孩子的方式，根节点要从数组的0处开始。
5. 根据不同的需求,每个节点(区间)维护的信息不同，可能是一个值，或是两个值，甚至是
   一个数组或一棵树。
//这里以区间最大最小值为例:
#include <vector>
#include <stdio.h>
#include <iostream>
using namespace std;

struct Node
{
    int max,min;    //区间信息,可自定义
    int left,right;
    int mid()
    {
        return (left+right)/2;
    }
};

static const int MAXN = 50000; //自行修改
Node tree[MAXN*4];  //注意开4倍空间

void build(int root,int left,int right) //建立线段树
{
    tree[root].max=-1;      //初始化
    tree[root].min=0xfffffff;
    tree[root].left=left;
    tree[root].right=right;
    
    if(left!=right)
    {
        build(root*2+1,left,tree[root].mid());
        build(root*2+2, tree[root].mid()+1, right);
    }
}

void update(int root,int k,int v)   //将以root为根的区间中k处的值改为v
{
    if(tree[root].left==tree[root].right)
    {
        tree[root].max=v;
        tree[root].min=v;
        return;
    }
    
    //在递归之前就改变父区间的信息
    tree[root].max=tree[root].max<v?v:tree[root].max;
    tree[root].min=tree[root].min>v?v:tree[root].min;
    
    if(k<=tree[root].mid())
    {
        update(root*2+1,k,v);
        return;
    }
    if(k>tree[root].mid())
    {
        update(root*2+2, k, v);
        return;
    }
}

Node query(int root,int l,int r)    //在以root为根的区间中查找[l,r]区间的信息
{
    Node t;
    if(tree[root].left==l&&tree[root].right==r)
    {
        t.max = tree[root].max;
        t.min = tree[root].min;
        return t;
    }
    if(r<=tree[root].mid())
    {
        return  query(root*2+1, l, r);
    }else if(l>tree[root].mid())
    {
        return  query(root*2+2, l, r);
    }else
    {
        Node a = query(root*2+1, l, tree[root].mid());
        Node b = query(root*2+2, tree[root].mid()+1, r);
        a.max=a.max>b.max?a.max:b.max;
        a.min=a.min<b.min?a.min:b.min;
        return a;
    }
}

ADD:上面的模板只能一次更新一个值，如果想一次对一个区间做同一种更新则效率太低，
    下面这个模板中的add函数可以高效的进行这种操作。
    (这里以求和为例子)
_________________________________________________________________
static const int MAX = 100010;

struct Node
{
    long long sum,inc;
    int left,right;
    int mid()
    {
        return (left+right)/2;
    }
};

Node tree[MAX*4];

void init_range(int root,int left,int right)
{
    tree[root].sum=0;
    tree[root].inc=0;
    tree[root].left=left;
    tree[root].right=right;
    if(left!=right)
    {
        init_range(root*2+1, left, tree[root].mid());
        init_range(root*2+2, tree[root].mid()+1, right);
    }
}

void update(int root,int k,long long v)
{
    if(tree[root].left==tree[root].right)
    {
        tree[root].sum=v;
        return;
    }
    //在递归之前就改变父区间的信息
    tree[root].sum+=v;
    
    if(k<=tree[root].mid())
    {
        update(root*2+1,k,v);
        return;
    }
    if(k>tree[root].mid())
    {
        update(root*2+2, k, v);
        return;
    }
}

//上面的和之前的模板都一样，而下面的add与query则不同
void add(int root,int left,int right,long long inc)
{
    //1.完全覆盖则不往下带，直接往inc上加，然后结束
    if(tree[root].left==left&&tree[root].right==right)
    {
        tree[root].inc+=inc;
        return;
    }
    
    //2.否则就先处理该区间原本的inc再处理当前参数中的的inc
    if(tree[root].inc!=0)
    {
        tree[root].sum+=
            tree[root].inc*(tree[root].right-tree[root].left+1);
        
        add(root*2+1,tree[root].left,
            tree[root].mid(),
            tree[root].inc);
        add(root*2+2,tree[root].mid()+1,
            tree[root].right,
            tree[root].inc);
        tree[root].inc=0;
    }
    
    tree[root].sum+=(right-left+1)*inc;
    
    //3.之后分割区间并往下带inc
    if(left>tree[root].mid())
        add(root*2+2, left, right, inc);
    else if(right<=tree[root].mid())
        add(root*2+1, left, right, inc);
    else
    {
        add(root*2+1,left,tree[root].mid(),inc);
        add(root*2+2, tree[root].mid()+1, right, inc);
    }
}


long long query(int root,int left,int right)
{
    //1.先处理当前区间的inc
    if(tree[root].inc!=0)
    {
        if(tree[root].left==tree[root].right)
        {
            tree[root].sum+=tree[root].inc;
            tree[root].inc=0;
        }else
        {
            tree[root].sum+=tree[root].inc*
                (tree[root].right-tree[root].left+1);
            add(root*2+1,
                tree[root].left,
                tree[root].mid(),
                tree[root].inc);
            add(root*2+2,
                tree[root].mid()+1,
                tree[root].right,
                tree[root].inc);
            tree[root].inc=0;
        }
    }
    
    //2.之后和普通的查询一样
    if(tree[root].left==left&&tree[root].right==right)
        return tree[root].sum;
    if(left>tree[root].mid())
        return query(root*2+2, left, right);
    if(right<=tree[root].mid())
        return query(root*2+1, left, right);
    return query(root*2+1, left, 
    	tree[root].mid())+query(root*2+2, tree[root].mid()+1, right);
}



F: 树状数组
_________________________________________________________________

1. 功能为线段树的子集,只适用于对定长区间和的查询和对单点的修改,不适用于区间修改
2. 与线段树不同,区间起始点必须从1开始。

static const int MAX = 100010;  //自行修改区间长度

int C[MAX+1];   //为了使范围为[1,MAX]

void init()
{
    memset(C, 0, sizeof(C));
}
int query(int n)    //  求[1,n]的和
{
    int sum = 0;
    while(n>0)  //注意边界
    {
        sum+=C[n];
        n-=n&-n;    //注意是减lowbit
    }
    return sum;
}
void add(int k,int v)   //将k点地值加上v
{
    while(k<=MAX)   //注意边界
    {
        C[k]+=v;
        k+=k&-k;    //注意是加lowbit
    }
}


G:trie树(待完善)
_________________________________________________________________
#include <vector>
#include <stdio.h>
#include <string.h>
#include <iostream>
#include <algorithm>
using namespace std;

static const int MAXLEN = 15;

struct Node
{
    char *p;    //
    
    Node *sub[26];  //
    Node()
    {
        p = NULL;
        for(int i=0;i<26;i++)   //
            sub[i]=NULL;
    }
};

struct trie
{
    Node *root;
    trie()
    {
        root = new Node;
    }
    
    void insert_str(char *s, char *content) //
    {
        Node *p = root;
        int c;
        for(int i=0;i<strlen(s);i++)
        {
            c=(int)(s[i]-'a');  //
            if(p->sub[c]==NULL)
            {
                p->sub[c]=new Node;
            }
            p=p->sub[c];
        }
        p->p= new char[MAXLEN];   //
        for(int i=0;i<strlen(content);i++)
            p->p[i]=content[i];
    }
    
    Node * search(char *s)
    {
        Node *p = root;
        int c;
        for(int i=0;i<strlen(s);i++)
        {
            c=(int)(s[i]-'a');
            if(p->sub[c]==NULL)
                return NULL;
            p=p->sub[c];
        }
        if(p!=NULL)
            return p;
        else
            return NULL;
    }
    
    void pre_order(Node *root)
    {
        if(root!=NULL)
        {
            if(root->p!=NULL)
            {
                printf("%s\n",root->p);
            }
            for(int i = 0;i<26;i++) //
                pre_order(root->sub[i]);
        }
    }
};

int main()
{
    trie tree;
    char a[30],b[15],c[15];
    while(gets(a)&&a[0]!='\0')
    {
        sscanf(a,"%s %s",b,c);
        tree.insert_str(c, b);
    }
    char s[15];
    while(gets(s)&&s[0]!='\0')
    {
        Node *p=tree.search(s);
        if(p==NULL)
        {
            printf("eh\n");
        }else
        {
            if(p->p!=NULL)
                printf("%s\n",p->p);
            else
                printf("eh\n");
        }
        
    }
    return 0;
    
}






通用算法
_________________________________________________________________
_________________________________________________________________
。。。。


数学方法
_________________________________________________________________
_________________________________________________________________



A:求最大公约数
_________________________________________________________________

欧几里得算法

int GCD(int a, int b) {
	int t; 
	while(b > 0) {
		t = a % b;
		a = b;
		b = t;
	} 
	return a;
}

递归版：

int GCD(int a,int b)
{
    if(b==0) return a;
    else return GCD(b,a%b);
}

拓展的欧几里得算法
1.因为对于两个数a,b,必存在x,y使ax+by=GCD(a,b),有时不仅要求a,b的最大公约数
  还要求如何得到这个最大公约数,即求x,y的值，这时用拓展的欧几里得算法。
2.这里使用了递推

struct Node
{
    int x,y;
    Node(int tx,int ty)
    {
        x=tx;
        y=ty;
    }
};

Node extGCD(int a,int b)
{
    if(b==0)
        return Node(1,0);
    else
    {
        Node t = extGCD(b,a%b);
        return Node(t.y,t.x-(a/b)*t.y);
    }
}


B:求最小公倍数：
_________________________________________________________________

x*y/GCD(x,y);


C:素数判断:
_________________________________________________________________

C1:判断一个数是否为素数

bool is_prime(int u){
    if(u==0||u==1)	return false;
    if(u==2)		return true;
    if(u%2==0)		return false;
    for(int i=3;i<=sqrt(u);i=i+2)
        if(u%i==0)	return false;
    return true;
}

C2:判断区间[1,n]内的所有数是否为素数：素数筛法
static const int N = 10000;

int primeList[N+10];

void range_prime()
{
    int i;
    for(i=1;i<=N;i++)
        primeList[i]=true;
    
    primeList[1]=false;
    for(i=2;i<=N;i++)
    {
        if(primeList[i]==true)
        {
            for(int j=2*i;j<=N;j=j+i)
                primeList[j]=false;
        }
    }
}
ADD:使用位图可减少内存使用和简化初始化操作
    排除偶数,只考虑奇数可减少一半内存


C3:判断区间[a,b]内的所有数是否为素数



D:快速幂运算
_________________________________________________________________
1. 快速求解(a^b)%p的问题

int quick_pow(int a,int b,int p)
{
    int ans=1;
    a=a%p;
    
    while(b)
    {
        if(b&1)
        {
            ans=(ans*a)%p;
        }
        b=(b>>1);
        a=(a*a)%p;
    }
    return ans;
}





组合求余问题（待完善）
_________________________________________________________________
求C(m,n)%p的问题

1. 当0<m<=n<1000时，可简单采用杨辉三角计算
2. 当0<m<=n<10^6，p为素数时，可采用逆元计算方法
3. 当0<m<=n<10^18, 1<p<10^5且p为素数时，可采用lucas定理

LL C(LL n, LL m)
{
    if(m > n) return 0;
    LL ans = 1;
    for(int i=1; i<=m; i++)
    {
        LL a = (n + i - m) % p;
        LL b = i % p;
        ans = ans * (a * quick_mod(b, p-2) % p) % p;
    }
    return ans;
}

LL Lucas(LL n, LL m)
{
    if(m==0) return 1;
    return C(n%p,m%p) * Lucas(n/p, m/p) % p;
}


常见子问题
_________________________________________________________________
_________________________________________________________________


求逆序对数,O(nlogn)时间复杂度
_________________________________________________________________
1. 先给序列按位置进行标号，再连同标号一起排序，对排好序的序列按值进行离散化,之
   后再根据位置标号将离散后的值放入新序列中。从新序列第一个值开始，以值作为下
   标建立BIT，每处理一个数，将其放入BIT中，并使其值加1，该数字作为下标的BIT
   从1到该下标的和就是位于该数字之前(包括该数字)的值小于等于该数字的个数。

#include <vector>
#include <stdio.h>
#include <string.h>
#include <iostream>
#include <algorithm>
using namespace std;

static const int MAX = 500010;

int c[MAX+1];
int n;  //用于保存序列实际长度

void init()
{
    memset(c, 0, sizeof(c));
}

long long sum(int n)
{
    long long ans = 0;
    while(n>0)
    {
        ans+=c[n];
        n-=n&-n;
    }
    return ans;
}

void add(int k,int v)
{
    while(k<=n)
    {
        c[k]+=v;
        k+=k&-k;
    }
}
//-------------------------------上面是BIT
struct Node
{
    int v;
    int pos;
};

bool comp(Node a,Node b)
{
    return a.v<b.v;
}

Node num[MAX+1];

int new_num[MAX+1];

int main()
{
    scanf("%d",&n);
    
    int i;
    for(i=1;i<=n;i++)
    {
        scanf("%d",&num[i].v);
        num[i].pos=i;   //按位置标号
    }
    sort(num+1, num+n+1, comp);
    
    int t = 1;
    new_num[num[1].pos]=1;  //按值进行离散
    for(i = 2;i<=n;i++)
    {
        if(num[i].v>num[i-1].v)
            t++;
        new_num[num[i].pos]=t;  //按值进行离散
    }
    init();
    long long s=0;
    for (i=1; i<=n; i++) {
        add(new_num[i], 1);     //以new_num[i]的值为下标的数字个数加1
        s+=i-sum(new_num[i]);   //i-sum(new_num[i])才是逆序对个数
    }
    printf("%lld\n",s);
    
    return 0;
}





