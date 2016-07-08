# coding: utf-8

# io分为同步IO和异步IO，这里讲的是同步IO


# 文件读写
# ------------------------------------------------------------
try:    # 可能产生IOError
    f = open('filePath','r')
    content = f.read()
#   content = f.write('hello')
finally:
    if f:
        f.close()

# read()一次读完, readline()一次读一行, readlines()一次读完，并按行返回一个list
# open中的第二个参数：'r':按ASCII码读，'rb':按二进制读，'w':写文件
# 字符编码:open('xx','r')默认按ASCII码读,但如果是其它的编码方式，就要按照下面的方法：
'''
f = open('xxx','rb')
content = f.read().decode('gbk')    # 先按二进制读,再进行解码
'''


# 目录操作
# ------------------------------------------------------------
