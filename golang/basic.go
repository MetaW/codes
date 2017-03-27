package main

import "fmt"
import "math"

const pi = 3.1415

func swap(x int, y int) (int, int) {
	return y, x
}

func deferFunc() {
	defer fmt.Println("aaa")
	defer fmt.Println("bbb")
	fmt.Println("ccc")
}

// lambda
var add = func(x int, y int) int { // int * int -> int
	return x + y
}

var adder = func() func(int) int {
	sum := 0
	return func(x int) int {
		sum += x
		return sum
	}
}

func main() {
	var i = int(math.Sqrt(16))
	var x = 123
	var y = 345
	x, y = swap(x, y)
	fmt.Println("nima", i+x+y)

	var sum = 0
	for i = 0; i < 10; i++ {
		sum = sum + i
	}
	fmt.Println(sum)

	sum = 0
	for sum < 10 { //for as while
		sum = sum + 1
	}
	fmt.Println(sum)

	var xx = 123
	switch xx {
	case 50:
		fmt.Println("50")
	case 100:
		fmt.Println("100")
	default:
		fmt.Println(xx)
	}

	deferFunc()

	var x1 int = 1234
	var px *int = &x1 //let px: ref int = newref x1
	fmt.Println(*px)  // deref px

	var po = point{2, 3}
	fmt.Println(po, po.x)

	var arr [3]int
	arr[0] = 12
	arr[1] = 23
	arr[2] = 34
	fmt.Println(arr)

	//map[type]type
	var mp = make(map[string]point)
	mp["first"] = point{1, 2}
	mp["second"] = point{2, 3}
	fmt.Println(mp)

	fmt.Println(add(3, 5))
	fmt.Printf("%T\n", add)

	var tt = point{3, 5}
	tt.Scale(2)
	fmt.Println(tt.Abs()) //!!!
}

// data abstraction
// top level : letrec binding
type point struct {
	x int
	y int
}

// receiver (go does not have class, but you can add method to type)
func (t point) Abs() float64 { // add method Abs() to type point
	return math.Sqrt(float64(t.x*t.x + t.y*t.y))
}

// pointer receiver : if you want to change the value of the receiver
// pointer receivers are more common than value receivers.
func (t *point) Scale(i int) {
	t.x = t.x * i
	t.y = t.y * i
}

//There are two reasons to use a pointer receiver.
//The first is the method can modify the value that its receiver points to.
//The second is to avoid copying the value on each method call.
//This can be more efficient if the receiver is a large struct, for example.
