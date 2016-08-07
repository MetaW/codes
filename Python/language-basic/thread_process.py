# coding: utf-8
'''
Unix/Linux操作系统提供了一个fork()系统调用，它非常特殊。普通的函数调用，
调用一次，返回一次，但是fork()调用一次，返回两次，因为操作系统自动把当前
进程（称为父进程）复制了一份（称为子进程），然后，分别在父进程和子进程内返回。

子进程永远返回0，而父进程返回子进程的ID。这样做的理由是，一个父进程可以fork出
很多子进程，所以，父进程要记下每个子进程的ID，而子进程只需要调用getppid()就
可以拿到父进程的ID。
'''

# 创建一个进程, only work on Linux/Unix/Mac
#--------------------------------------------------------
import os

# print("process %s start ..." % os.getpid())
#
# pid = os.fork()
#
# if pid == 0:
#     print("I am a child process %s and my parent pid is %s" % (os.getpid(), os.getppid()))
# else:
#     print("I have just create a precess %s and my id is %s" % (pid, os.getpid()))



# 创建一个进程，更通用的方法
#--------------------------------------------------------
from multiprocessing import Process
# # import os

def run_process(name):  # 子进程运行的函数
    print("I am the child process %s my name is %s and my parent is %s" % (os.getpid(), name, os.getppid()))

if __name__ == '__main__':
    print("parent process is %s" % os.getpid())
    p = Process(target = run_process, args = ('test',))

    p.start()
    p.join()    #join()方法可以等待子进程结束后再继续往下运行，通常用于进程间的同步。

    print("child process finished!")


# 在python中通过终端运行别的程序
#--------------------------------------------------------
import subprocess

result = subprocess.call(["python3","debug.py"])
print(result)



# 进程间的通信
#--------------------------------------------------------
from multiprocessing import Queue
import time, random

def run_write(param):
    print("Process %s will write" % os.getpid())
    for t in ['A','B','C']:
        print("put %s to queue!" % t)
        param.put(t)
        time.sleep(random.random())

def run_read(param):
    print("Process %s will read" % os.getpid())
    while True:
        value = param.get(True)
        print("get %s from queue!" % value)

if __name__ == "__main__":
    q = Queue()
    pw = Process(target = run_write, args = (q,))
    pr = Process(target = run_read, args = (q,))

    pw.start()
    pr.start()

    pw.join()       # 等待pw运行完
    pr.terminate()  # pr是死循环，只能terminate才能结束
