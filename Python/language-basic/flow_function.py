
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
while True:
	print(x)
	if x > 20:
		break


#continue
#------------------------------------------------

for i in range(1,10):
	if i = 5:
		continue
	print(i)








