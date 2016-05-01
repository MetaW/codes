# coding: utf-8
from bs4 import BeautifulSoup
import re
import urlparse


class HtmlParser(object):
    def __init__(self):
        pass

    def parse(self, page_url, html_cont):
        if page_url is None or html_cont is None:
            return

        soup = BeautifulSoup(html_cont, 'html.parser', from_encoding='utf-8')
        newUrls = self._getNewUrls(page_url, soup)
        newData = self._getNewData(page_url, soup)
        return newUrls, newData



    def _getNewUrls(self, page_url, soup):
        newUrls = set()
        links = soup.find_all('a', href = re.compile(r"/view/\d+\.htm"))
        for link in links:
            newUrl = link['href']

            #
            newFullUrl = urlparse.urljoin(page_url, newUrl)
            newUrls.add(newFullUrl)

        return newUrls

    def _getNewData(self, page_url, soup):
        resData = {}

        resData['url'] = page_url
        #soup是一个节点树,具体要寻找什么样的信息要靠自己查看待爬页面的源代码，看看要爬内容
        #所在的标签名，class名等，得到的可能是一个子树，如本例子的情况，因此还有进一步从该
        #子树中活的自己想要的内容所在的节点。
        titleNode = soup.find('dd', class_="lemmaWgt-lemmaTitle-title").find("h1")

        resData['title'] = titleNode.get_text()

        summaryNode = soup.find('div', class_="lemma-summary")

        resData['summary'] = summaryNode.get_text()

        return resData
