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






# 实例属性，类属性
# ------------------------------------------------------------
# 在__init__中定义的为实例属性，在class中直接定义的是类属性
class NewClass(object):

	attr = "haha" 	# attr 是类属性

	def __init__(self, arg):
		self.arg = arg 	# arg 是实例属性
		






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

# ---------- isinstance(a,b)
# (instance, class) -> bool
# 判断一个对象是否是某个类(或其子类)的实例



# ---------- type
# (instance) -> type
# 判断数据的类型

aa = type(123) 
# aa = int

bb = type("haha")
# bb = str

cc = type(int)
# cc = type

dd = type(type)
# dd = type

hh = type([1,2,3])
# hh = list

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


	

# ---------- dir(a)
# anything -> list
# dir返回任何变量(广义上)的所有能够访问的东西，包括对象，模块，函数等


ii = dir(Dog("abc"))

'''
ii = ['_Animal__name', '__class__', '__delattr__', 
	  '__dict__', '__doc__', '__format__', '__getattribute__', 
	  '__hash__', '__init__', '__module__', '__new__', 
	  '__reduce__', '__reduce_ex__', '__repr__', '__setattr__', 
	  '__sizeof__', '__str__', '__subclasshook__', '__weakref__', 
	  'getName', 'run']
'''

jj = dir(lambda x : x + x)

'''
jj = ['__call__', '__class__', '__closure__', '__code__', 
	  '__defaults__', '__delattr__', '__dict__', '__doc__', 
	  '__format__', '__get__', '__getattribute__', 
	  '__globals__', '__hash__', '__init__', '__module__', 
	  '__name__', '__new__', '__reduce__', '__reduce_ex__', 
	  '__repr__', '__setattr__', '__sizeof__', '__str__', 
	  '__subclasshook__', 'func_closure', 'func_code', 
	  'func_defaults', 'func_dict', 'func_doc', 'func_globals', 
	  'func_name']
'''




# ---------- hasattr(a,b)
# (anything, str) -> bool
# 测试一个变量是否有属性str, 其实就是检查 str 是否在 dir(anything)当中

kk = hasattr(Dog("haha"), "run")
# kk = True

ll = hasattr(Dog("haha"), "__class__")
# ll = True



# ---------- getattr(a,b) 
# (anything, str) -> attribute
# getattr 返回 anything 的 名为str的attribute，若没有该attri即
# hasattr返回False，则getattr会抛出异常

mm = getattr([1,2,3],"__len__")()
# mm = 3


# ---------- setattr(a,b,c)
# (anything, str, value) -> ()
# pass 



