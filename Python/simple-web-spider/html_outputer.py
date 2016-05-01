# coding: utf-8

class HtmlOutputer(object):
    def __init__(self):
        self.datalist = []

    def collectData(self, data):
        if data is None:
            return

        self.datalist.append(data)


    def outputHtml(self):
        fout = open('/Users/wanglulu/Desktop/output.html', 'w')
        fout.write("<html>")
        fout.write("<body>")
        fout.write("<table>")

        for data in self.datalist:
            fout.write("<tr>")
            fout.write("<td>%s</td>" % data['url'])
            fout.write("<td>%s</td>" % data['title'].encode('utf-8'))
            fout.write("<td>%s</td>" % data['summary'].encode('utf-8'))
            fout.write("</tr>")

        fout.write("</table>")
        fout.write("</body>")
        fout.write("</html>")

        fout.close()
