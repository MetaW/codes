def func1(f):
    def ff(x, y):
        return x+y
    return ff

@func1
def func2(x, y):
    return x-y

'''
func2(5,3) = 8
'''

#### desugar to:
def func1(f):
    def ff(x, y):
        return x+y
    return ff

def func2(x, y):
    return x-y

func2 = func1(func2)
'''
func2(5, 3) = 8
'''

'''
func1 takes a closure 1 and return a closure 2
closure 1 and closure 2 must have the same number of parameter

decorator is a syntex sugar for a high order function thats function as input and returns
another function
'''