from urllib import request as req

# 下载所有已经做完的Lean 4数据库项目列表origin (html格式)
def openWeb(url, head):
    web = req.Request(url, headers=head)
    return req.urlopen(web).read().decode()

if __name__ == '__main__':
    # 网址、文件夹
    url = 'http://101.200.15.5/math-mark/task/list?page=1&pageSize=4000&courseId=2&name=&status=done'
    dir = 'D:/VScodeProjects/PythonProjects/DownloadLean/Code/'
    # 访问头
    head = dict()
    with open(dir + '../--Head1', 'r') as f:
        keyVal = f.read().split('\n\n')
        f.close()
    for kv in keyVal:
        (key, val) = kv.split('\n')
        head[key] = val
    # 读取
    with open(dir + 'origin', 'w', encoding='utf-8') as f:
        f.write(openWeb(url, head))
        f.close()
    