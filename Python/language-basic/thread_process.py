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
    q = Queue() # 创建一个队列
    pw = Process(target = run_write, args = (q,))   #把队列传入子进程，使其能够访问
    pr = Process(target = run_read, args = (q,))

    pw.start()
    pr.start()

    pw.join()       # 等待pw运行完
    pr.terminate()  # pr是死循环，只能terminate才能结束




'''
多线程和多进程最大的不同在于，多进程中，同一个变量，各自有一份拷贝
存在于每个进程中，互不影响，而多线程中，所有变量都由所有线程共享，
所以，任何一个变量都可以被任何一个线程修改，因此，线程之间共享数据
最大的危险在于多个线程同时改一个变量，把内容给改乱了。
'''

# 创建线程
#--------------------------------------------------------
import threading

def run_something():
    print("thread %s is running!" % threading.current_thread().name)
    time.sleep(2)
    print("thread %s is end!" % threading.current_thread().name)

if __name__ == "__main__":
    print("thread %s is running!" % threading.current_thread().name)

    t = threading.Thread(target=run_something, name="new_thread")
    t.start()
    t.join()

    print("thread %s is end!" % threading.current_thread().name)



# 线程锁
#--------------------------------------------------------
# 涉及对共享数据进行更新的方法(事务)，为防止多个线程同时执行所带来的
# 错误，应该对这类方法进行加锁，使每次最多只能有一个线程在执行该函数

balance = 100

lock = threading.Lock() #创建一个锁

def change_balance(n):  #该函数为更新共享变量balance的方法，需要加锁
    lock.acquire()  # 上锁

    global balance  # 被锁住的代码
    balance = balance + n
    balance = balance - n

    lock.release()  # 解锁


def run_many_time(n):
    for i in range(10000):
        change_balance(n)

if __name__ == '__main__':
    t1 = threading.Thread(target=run_many_time, args=(5,))
    t2 = threading.Thread(target=run_many_time, args=(8,))

    t1.start()
    t2.start()
    t1.join()
    t2.join()

    print(balance)
