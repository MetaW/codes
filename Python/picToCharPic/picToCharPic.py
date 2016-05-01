# coding: utf-8
'''
transform a pictrue to a character picture

need to install a pacage: Pillow

sudo pip install Pillow

'''

from PIL import Image

asicc_char = list("#@B%8&WM$*oahkbdpqwmZO0QLCJUYXzcvunxrjft/\|()1{}[]?-_+~<>i!lI;:,\"^`'. ")

def trans_to_char(r,g,b,alpha=256):
	if alpha == 0:
		return ' '
	length = len(asicc_char)
	gray = int(0.2126 * r + 0.7152 * g + 0.0722 * b)
	ind = int(length*gray/257)
	return asicc_char[ind]


imgf = raw_input("输入文件:")
outf = raw_input("输出文件:")
width = int(raw_input("宽度:"))
height = int(raw_input("高度:"))

img = Image.open(imgf)	#open a image
img = img.resize((width,height), Image.NEAREST)	#resize the image
txt = ""

for i in range(height):
	for j in range(width):
		txt += trans_to_char(*img.getpixel((j,i)))	#get rgb value from image
	txt = txt + '\n'

out = open(outf,'w')	#write to file
out.write(txt)
out.close()






