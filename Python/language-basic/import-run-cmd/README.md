### 关于文件的import，执行，和在命令行中交互式操作的说明

----
### python的代码共可分为三类：

> #### 1.定义，包括变量定义，函数定义，类定义等
> #### 2.执行，即表达式赋值，函数调用等
> #### 3.查看某变量的值，即直接打改变量的名

### 其中

* 在命令行中定义，执行，和查看变量都是有效的
* 执行py文件时，定义和执行是有效的，而查看变量值会自动忽略
* import一个文件时定义是有效的，执行也是有效的，即仅仅import就有可能会打印或执行一些函数(注 意：这里的import不仅指在文件中，在命令行中也一样)

### 因此
* 查看变量是专为交互式命令行设计的，相当于print(某变量)，在import和执行中没有效果。
* 一般作为库文件(被主文件引入)的文件，不再其中写执行类型的代码，而只是定义一些函数，变量或类，供主文件使用。

### 注意
* 在一个文件中使用引入文件中的变量，函数或类时要在其前面加上文件名及‘.’来访问，eg：subFile.someFunc(para)

### 在命令行执行python文件
* 可以使用"python filename.py"来执行
* 也可以用"./filename.py"来执行，但此方法要求在文件第一行加上#!/usr/bin/env python，并且文件要赋予执行的权利

### import 与 reload
* import用的很多就不多说
* reload在REPL中调试时很常用,由于文件只能import一次，但很多时候我们修改代码后要重新import，这时只能用reload
* import与reload的用法不同:
``` python
  import filename
  reload(filename)
```

---
### module, package
* 一个.py文件就是一个模块(module)
* 若模块名字之间有冲突,可以通过包(package)来组织模块
* 一个包就是一个文件夹,但该文件夹下要有一个__init.py__的文件，否则，Python就把这个目录当成普通目录，而不是一个包。__init__.py可以是空文件，也可以有Python代码，因为__init__.py本身就是一个模块，而它的模块名就是mymodule.

eg:

```
other.py
haha.py
mymodule
	|--	__init.py__
	|--	abc.py
	|--	xyz.py
```
* 放在包内的模块引入时，名称变为 mymodule.abc, mymodule.xyz 而不再是 abc, xyz 了


### 模块中变量的作用域

* 正常的函数和变量名是public的, 可以在模块外部引用, eg: abc, x123, func()
* 前缀为_的变量是private的,只应该在模块内部被访问, eg: _abc, _x123, _func()
* 注意: 即使加了前缀_,也能够从外部访问到，因此说是“不应该”而不是“不能”，但这访问它们是错误的编程风格。

### 模块搜索路径
import 一个模块时, Python解释器会搜索当前目录、所有已安装的内置模块和第三方模块，搜索路径存放在sys模块的path变量中
