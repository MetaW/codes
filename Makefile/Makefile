#	1.	基本例子
#	2.	基本例子
#	3.	特殊任务的target
#	4.	.PHONY
# 5.	变量
# 6.	使用目录
# 7.	生成多个目标
# 8.	一些特殊符号
# 9.	@命令
# 10.	shell命令的做用范围
# 11.	在makefile中make别的工程
# 12.	定义命令包
# 13.	变量的修改与追加
# 14.	通配符 %


# 1.基本例子
#=============================================
#target: dependent files
#[tab]shell script

#输入“make”后，默认只执行第一个target的script,但如果其dependent files没有找到或
#却少，就去找与却少的file名字一样的target，并执行其script如此递归。
#如果一个文件存在，但其target中的dependent文件比它新，那么也重新执行dependent
#文件对应的target，来更新该target对应的文件


some_binary1:
	echo "some_binary1"

other1.txt:	# other1.txt没有被依赖到，该target默认不会执行
	echo "other1.txt"


# 2.基本例子
#-------------------------------------------
some_binary2: other2.txt
	touch "some_binary2"

other2.txt:	# other2.txt不会被创建，因此每次make，该target都会被执行
	echo "we do not create other2.txt"


# 3.特殊任务的target
#-------------------------------------------
# "make target_name"可以指定执行一个target,通常完成一些特殊任务，如清空一些文件
some_binary3: clean
	touch some_binary3

clean:
	echo "clean is not a key word!!!"
	touch clean

real_clean:
	rm some_binary3
	rm clean



# 4. .PHONY
#-------------------------------------------
# 大多数情况下一个target与一个文件名相对应，其script中为该文件的生成命令，
# 但有时我们需要一些完成特殊任务的target，如clean，他们并不与任何文件相对应，
# 为了把它们与一般的target区分，我们在这些特殊的target前加上 .PHONY: target_name,
# 当然这不是必须的，只是为了方便阅读,避免混淆。
some_binary4:
	touch some_binary4


.PHONY: author
author:
	echo "This file is written by wanglulu"

.PHONY: clean_file
clean_file:
	rm some_binary4



# 5.变量
#-------------------------------------------
# 可以定义一些变量，以提供方便:
# 定义: variable = value1 value2 value3
# 使用: $(variable)
# 这里的variable其实是宏替换
files = file1 file2

some_binary5: $(files)
	touch some_binary5

file1:
	touch file1

file2:
	touch file2

clean_all:
	rm $(files) some_binary5



# 6.使用目录
#-------------------------------------------
# target的依赖不仅可以是文件还可以是目录
some6: ../test
	touch some6

../test:
	mkdir ../test
	touch ../test/temp

clear6:
	rm some6
	rm ../test/temp
	rmdir ../test



# 7.生成多个目标
#-------------------------------------------
# 生成多个目标
# 在第一个目标中的依赖中写上多个目标，但不用写script
all: target1.x target2.x

target1.x:
	touch target1.x

target2.x:
	touch target2.x

clear7:
	rm target1.x target2.x


# 8. 一些特殊符号
#-------------------------------------------
# 特殊符号
#	$@	当前的target名字
#	$^	当前target的所有依赖文件的名字
#	$<	当前target的第一个依赖文件的名字
#	$?	当前target的所有更新过的依赖文件的名字


# 9. @命令
#-------------------------------------------
# @加在一个命令前，make时该命令不会被显示出来
some9: file9.txt
	@echo "this command will not be printed!"

file9.txt:
	@touch file9.txt

clear9:
	@rm file9.txt



# 10. shell命令的做用范围
#-------------------------------------------
# 同一行的命令是在一个shell内的，换行相当于重新开启一个shell
some10:
	cd ..
	echo `pwd`	#/Users/luluwang/Desktop/Makefile

	cd ..; echo `pwd`	#/Users/luluwang/Desktop

	cd ..; \
	echo `pwd`	#/Users/luluwang/Desktop




# 11. 在makefile中make别的工程
#-------------------------------------------
# 在makefile中make别的工程
all11: proj1 proj2	#proj1与proj2都是目录

proj1:
	cd proj1; make

proj2:
	cd proj2; make

# 12. 定义命令包
#-------------------------------------------
# 可以定义一串命令作为一个包，重复使用
define comm
	@echo "hello"
	@echo "target:" $@
	@echo "dependents:" $^
endef

all12: file12.txt fold12

file12.txt:
	$(comm)
	touch file12.txt

fold12:
	$(comm)
	mkdir fold12

clear12:
	rm file12.txt
	rmdir fold12

# 13.变量的修改与追加
#-------------------------------------------
# 当变量需要修改或追加内容时，用:=来定义
x13 := haha1
x13 += haha2	# x13 = haha1 haha2
y13 := $(x13)	# y13 = haha1 haha2
x13 := haha3	# x13 = haha3

some13:
	echo $(y13)
	echo $(x13)
	echo $(CC)

# 14. 通配符 %
#-------------------------------------------
# 通配符 % 能匹配0个或多个字符，使用它能带来方便
files14 = a1.x a2.x a3.x
all14: $(files14)

%.x:
	echo $@
	touch $@

clear14:
	rm a1.x a2.x a3.x
