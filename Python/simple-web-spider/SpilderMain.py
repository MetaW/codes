# -*- coding: utf-8 -*-

import url_manager
import html_downloader
import html_parser
import html_outputer


class SpiderMain(object):
    def __init__(self):
        #
        self.urls = url_manager.UrlManager()
        self.downloader = html_downloader.HtmlDownloader()
        self.parser = html_parser.HtmlParser()
        self.outputer = html_outputer.HtmlOutputer()

    def craw(self, root_url):
        count = 0

        #
        self.urls.addNewUrl(root_url)

        while self.urls.hasNewUrl() == True:
            if count == 200:
                break

            try:
                #
                newUrl = self.urls.getNewUrl()

                print(count)
                print(newUrl)
                #
                htmlContent = self.downloader.download(newUrl)

                #
                newUrls, newData = self.parser.parse(newUrl, htmlContent)

                #
                self.urls.addNewUrls(newUrls)
                self.outputer.collectData(newData)
                count += 1
            except:
                print("this page failed")

        self.outputer.outputHtml()

spider = SpiderMain()
spider.craw('http://baike.baidu.com/view/21087.htm')
