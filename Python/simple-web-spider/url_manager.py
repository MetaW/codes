# coding: utf-8

class UrlManager(object):
    def __init__(self):
        self.newUrls = set()
        self.oldUrls = set()


    def addNewUrl(self, url):
        if url is None:
            return
        if url not in self.newUrls and url not in self.oldUrls:
            self.newUrls.add(url)

    def addNewUrls(self, urls):
        if urls is None or len(urls) == 0:
            return

        for url in urls:
            self.addNewUrl(url)

    def hasNewUrl(self):
        if len(self.newUrls) == 0:
            return False
        else:
            return True
    
    def getNewUrl(self):
        newUrl = self.newUrls.pop()
        self.oldUrls.add(newUrl)
        return newUrl

