# -*- coding: utf-8 -*-
# 上面这句是为了在代码中可以使用中文,包括中文注释
#
#
import urllib2
import cookielib
import bs4
import re

"""------------------------------------------------------------
1.  网页下载demo
    这里使用Python自带的urllib2,如果需要更强大的功能可以使用第三方
    网页下载器,使用第三方模块需要安装
"""

def WebDownloader():
    url = "http://www.baidu.com"

    #第一种方法

    response1 = urllib2.urlopen(url)
    print(response1.getcode())
    print(response1.read())

    #第二种方法

    request = urllib2.Request(url)
    request.add_header("user-agent", "Mozilla/5.0")
    response2 = urllib2.urlopen(request)
    print(response2.getcode())
    print(response2.read())

    #第三种方法

    cj = cookielib.CookieJar()
    opener = urllib2.build_opener(urllib2.HTTPCookieProcessor(cj))
    urllib2.install_opener(opener)

    response3 = urllib2.urlopen(url)
    print(response3.getcode())
    print(cj)
    print(response3.read())


"""------------------------------------------------------------
2.  网页解析demo
    网页解析通常有以下几种方法

        模糊匹配
    1.使用正则表达式

        结构化解析:DOM树
    2.使用Python自带的html.parser
    3.使用第三方插件BeautifulSoup
    4.使用第三方插件lxml

    这里使用BeautifulSoup
    安装： 命令行中输入：sudo pip install python-bs4
          可能需要翻墙

"""

from bs4 import BeautifulSoup

def WebAnalyser():
    html_doc = """
    <html><head><title>The Dormouse's story</title></head>
    <body>
    <p class="title"><b>The Dormouse's story</b></p>

    <p class="story">Once upon a time there were three little sisters; and their names were
    <a href="http://example.com/elsie" class="sister" id="link1">Elsie</a>,
    <a href="http://example.com/lacie" class="sister" id="link2">Lacie</a> and
    <a href="http://example.com/tillie" class="sister" id="link3">Tillie</a>;
    and they lived at the bottom of a well.</p>

    <p class="story">...</p>
    """
    soup = BeautifulSoup(html_doc,'html.parser',from_encoding='utf-8')

    #获取所有连接
    links = soup.find_all('a')
    for link in links:
        print(link.name, link['href'], link.get_text())

    #根据属性值获取连接
    link_node = soup.find('a', href = 'http://example.com/elsie')
        #除了href还可搜索其他属性,如id,class_(由于class是关键字所以这里加了下划线)等
    print(link_node.name, link_node['href'], link_node.get_text())

    #利用正则表达式匹配属性值来获取连接
    link_node = soup.find('a', href = re.compile(r"ill"))
    print(link_node.name, link_node['href'], link_node.get_text())

