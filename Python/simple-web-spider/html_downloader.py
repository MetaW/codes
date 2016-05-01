# coding: utf-8
import urllib2

class HtmlDownloader(object):
    def __init__(self):
        pass

    def download(self, url):
        if url is None:
            return None

        response = urllib2.urlopen(url)

        #判断是否成功
        if response.getcode() != 200:
            return None

        return response.read()
