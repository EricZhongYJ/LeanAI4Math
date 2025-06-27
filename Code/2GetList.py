# 从origin中获取列表list
if __name__ == '__main__':
    dir = 'D:/VScodeProjects/PythonProjects/DownloadLean/1List/'
    with open(dir + 'origin', 'r', encoding='utf-8') as f:
        data = f.read()
        f.close()
    with open(dir + 'list', 'w', encoding='utf-8') as f:
        c = data.find('"name":"')
        while c > 0:
            a = data.find('"id":', c - 30)
            b = data.find(',', a + 5)
            d = data.find('",', c + 8)
            e = data.find('"md":', d)
            g = data.find('",', e + 6)
            f.write(data[a + 5:b] + '\n' + data[c + 8:d] + '\n' + data[e + 6:g] + '\n\n')
            c = data.find('"name":"', d + 1)