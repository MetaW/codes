# coding: utf-8


# assert
# -------------------------------------------------
# syntax
# assert bool-rexpession, "error message"
assert 1 < 2, "blabla"

x = 5
assert x == 5, "blabla"





# 单元测试
# -------------------------------------------------
# 使用单元测试来测试一个函数，一个类或一个模块的正确性。python本书
# 就有用于单元测试的模块: unittest。下面给出一个例子:



# 假设我们写了一个自己的数学类: Math

class Math(object):

	def __init__(self, name):
		super().__init__()
		self.__name = name

	def plus(self,a,b):
		return a + b

	def isEven(self,x):
		if x % 2 == 1:
			return False
		else:
			return True

	def gcd(self,a,b):
		if a > b:
			return self.gcd(b,a)
		else:
			t = b % a
			if t == 0:
				return a
			else:
				return self.gcd(t,a)

	def getName(self):
		return self.__name

# setUp于tearDown分别会在每一个test方法调用前后被执行,这在某些情况下，
# 如测试中有文件操作，数据库操作等情况时，将打开关闭操作写在这两个方法中，
# 就不用在每个测试函数中都写了。
	def setUp(self):
		print("test start!!!\n")

	def tearDown(self):
		print("test finished!!!\n")



# 现在我们对该类进行单元测试
import unittest

# 编写单元测试时，我们需要编写一个测试类，从unittest.TestCase继承。

class TestMath(unittest.TestCase):

	def test_init(self):
		a = Math("haha")
		self.assertTrue(isinstance(a,Math))

	def test_plus(self):
		a = Math("hehe")
		self.assertEqual(a.plus(3,5), 8)
		self.assertEqual(a.plus(9,0), 9)

	def test_isEven(self):
		a = Math("hehe")
		self.assertEqual(a.isEven(5), False)
		self.assertEqual(a.isEven(4), True)

	def test_gcd(self):
		a = Math("hehe")
		self.assertEqual(a.gcd(3,5), 1)
		self.assertEqual(a.gcd(4,8), 4)

	def test_getName(self):
		a = Math("hehe")
		self.assertEqual(a.getName(), "hehe")


# 以test开头的方法才是测试方法，不以test开头的方法不被认为是测试方法，测试的时候不会被执行



# 运行单元测试
if __name__ == '__main__':
    unittest.main()
# 之后运行该文件，就能显示出测试后的信息了, 只有测试类中形如 test_XXX 的方法才会被执行。

# !!! 一般测试类独自写在一个文件中
'''
之后在终端输入：python3 debug.py 就能得到以下结果:

.....
----------------------------------------------------------------------
Ran 5 tests in 0.001s

OK

'''


'''
单元测试的测试用例要覆盖常用的输入组合、边界条件和异常。

单元测试代码要非常简单，如果测试代码太复杂，那么测试代码本身就可能有bug。

单元测试通过了并不意味着程序就没有bug了，但是不通过程序肯定有bug。
'''
