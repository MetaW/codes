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



class Dog(Animal):	
	def __init__(self, name):
		super(Dog, self).__init__(name)

	def run(self):	# 函数重载
		print("Dog %s is runnig" % self.__name)



		