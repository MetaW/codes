# put this file in: /Users/luluwang/Desktop/Github/codes/Python/language-basic
# run this file in: <cwd>
# eg: python3 /Users/luluwang/Desktop/Github/codes/Python/language-basic/path.py

#========================= os.path
'''
path for find a file/resource
'''
import os
print("===== os.path")
#===== get source file abs path
print("1: ", __file__)
#=> <cwd>/???/path.py

print("2: ", os.path.abspath(__file__))
#=> /Users/luluwang/Desktop/Github/codes/Python/language-basic/path.py

#===== get source file abs dir
print("3: ", os.path.dirname(__file__))
#=> <cwd>/???/language_basic

print("4: ", os.path.dirname(os.path.abspath(__file__)))
#=> /Users/luluwang/Desktop/Github/codes/Python/language-basic

#===== get current dynamic path
print("5: ", os.path.abspath('.')) #=> <cwd>
print("6: ", os.getcwd())          #=> <cwd>

#===== get home dir
print("7: ", os.path.expanduser('~'))
#=> /Users/luluwang



#========================= sys.path
'''
PYTHONPATH: path for finding python packages
'''
import sys
print("===== sys.path")
print(sys.path)
#=> ['/Users/luluwang/Desktop/Github/codes/Python/language-basic', 
#    '/usr/local/Cellar/python/3.6.4_3/Frameworks/Python.framework/Versions/3.6/lib/python36.zip', 
#    '/usr/local/Cellar/python/3.6.4_3/Frameworks/Python.framework/Versions/3.6/lib/python3.6', 
#    '/usr/local/Cellar/python/3.6.4_3/Frameworks/Python.framework/Versions/3.6/lib/python3.6/lib-dynload', 
#    '/usr/local/lib/python3.6/site-packages', 
#    '/usr/local/lib/python3.6/site-packages/face_alignment-0.1.1-py3.6.egg', 
#    '/usr/local/opt/opencv/lib/python3.6/site-packages']

#===== add temporary path to PYTHONPATH: only for this program
# examples:
sys.path.append(os.path.dirname(__file__)+'/..')
sys.path.append('/User/luluwang/mylibs')
# or
sys.path.insert(0, '/User/luluwang/mylibs')


#===== add permanent path to PYTHONPATH
# insert the following code to .bashrc(ubuntu) or .profile(MacOS) file 
'''
export PYTHONPATH = $PYTHONPATH:'/User/luluwang/mylibs'
'''