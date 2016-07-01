# coding: utf-8


# create a class
# ------------------------------------------------------------
class ClassName(object):
	def __init__(self, attri1, attri2):
		self.attri1 = attri1
		self.attri2 = attri2
		self.attri3 = 0
		self.__private = "wll"

	def otherFunc(self, otherParams):
		pass

# 创建实例
ins = ClassName("haha", "hehe")

# __init__(..) 是初始化函数
# FatherClass如果没有就写 object
# 每个函数都第一个参数都必须为self, 但调用时不用为它传入参数
# 属性不用声明(因为弱类型)，但要在__init__中初始化后,才能在整个class中访问
# 前缀为__的方法和属性是 private 的，无法在外部访问, 否则就是 public 的




# 继承，多态，重载
# ------------------------------------------------------------
class Animal(object):
	def __init__(self, name):
		self.__name = name
		
	def run(self):
		print("Animal %s is running!" % self.__name)

	def getName(self):
		return self.__name



class Dog(Animal):	
	def __init__(self, name):
		super(Dog, self).__init__(name)	#super的固定写法

	def run(self):	# 函数重载
		print("Dog %s is runnig" % self.getName())


# 子类无法直接访问父类的private属性和方法
# 父类中只有public的属性和方法才能直接访问



# help functions 
# ------------------------------------------------------------

# isinstance(a,b)
# instance -> class -> bool
# 判断一个对象是否是某个类的实例


# type
# instance -> type
# 判断数据的类型

aa = type(123) 
# aa = int

bb = type("haha")
# bb = str

cc = type(int)
# cc = type

dd = type(type)
# dd = type

# 非基本类型时
import types

ee = type(max)
# ee == types.BuiltinFunctionType

ff = type(lambda x : x + x) 
# ff = types.LambdaType

def foo():
	return 123

gg = type(foo)

# gg = types.FunctionType


		
