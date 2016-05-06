# coding: utf-8


# if else
if 2>3:
	print("haha")
else:
	print("hehe")



#多分枝

score = 86
if score > 90:
	print("good")
else:
	if score > 80:
		print("normal")
	else:
		if score > 70:
			print("bad")
		else:
			print("stupid!")

#或
if score > 90:
	print("good")
elif score > 80:
	print("normal")
elif score > 70:
	print("bad")
else:
	print("stupid")


#for
#--------------------------------------------------

#遍历list,tuple,dist,set
li = [1,2,3,4]
for v in li:
	print(v)

#其它类似

#使用range
#range(n,m): 		[n,n+1,n+2,...m)
#range(n,m,step):	[n,n+step,n+2*step,...m)
for i in range(1,10,2):
	print(i)

#while
#-------------------------------------------------

x = 0
N = 10
while x < N:
	print(x)
	x = x + 1



#break
#-------------------------------------------------
while False:
	print(x)
	x = x + 1
	if x > 20:
		break


#continue
#------------------------------------------------

for i in range(1,10):
	if i == 5:
		continue
	print(i)




#函数
#------------------------------------------------
def max_num(a,b):
	if a>b:
		return a
	else:
		return b


#返回多值
def get_my_info():
	return "wll", 22, 1.70
	#实际返回的是("wll",22,1.70)

#调用
(name,age,tall) = get_my_info()

	#或
name2,age2,tall2 = get_my_info()


#默认参数
def power(x, n = 2):
	s = 1
	while n>0:
		s = s*x
		n = n - 1
	return s

def demofunc(a, b = 1, c = 2):
	return "haha"
	#默认参数必须放在最后

#调用含默认参数的函数
power(4,4)	#或 power(4, n=4)
power(4)



#个数可变的参数





