from urllib import request as req
from os import mkdir
from time import sleep

# 从list中逐个下载Lean证明
def openWeb(url, head):
    web = req.Request(url, headers=head)
    return req.urlopen(web).read().decode()

if __name__ == '__main__':
    # 网址、文件夹
    url = 'http://101.200.15.5/math-mark/response/list?page=1&pageSize=10000&taskId=%s'
    dir = 'D:/VScodeProjects/PythonProjects/DownloadLean/LeanFile/'
    try: mkdir(dir)
    except: pass
    # 访问头
    head = dict()
    with open(dir + '../--Head1', 'r') as f:
        keyVal = f.read().split('\n\n')
        f.close()
    for kv in keyVal:
        (key, val) = kv.split('\n')
        head[key] = val
    # 读取
    with open(dir + '../Code/list', 'r', encoding='utf-8') as f:
        data = f.read().split('\n\n')[:-1]
        f.close()
    # 下载 todo 调整范围 - 3331个
    for i in range(80, 100):
        info = data[i].split('\n')
        leanOri = openWeb(url % info[0], head)
        with open(dir + f'{i + 1:04d}.lean', 'w', encoding='utf-8') as f:
            # 获取每个题目的描述、证明
            a = leanOri.find('import Mathlib\\n')
            if a == -1: a = leanOri.find('"formalProof":"') - 1
            b = leanOri.find('",', a + 2)
            c = leanOri.find('"informalProof":"')
            d = leanOri.find('",', c)
            f.write('import Mathlib\n')
            discribe = info[2].replace('\\n', '\n').replace('\\\\', '\\').replace('\n\n', '\n')
            f.write(f'/-! Question:\n{discribe}\n-/\n')
            f.write(leanOri[a + 16:b].replace('\\n', '\n').replace('\\\\', '\\'))
            informal = leanOri[c + 17:d].replace('\\n', '\n').replace('\\\\', '\\').replace('\n\n', '\n')
            if leanOri[d - 1] != 'n': f.write('\n')
            if len(informal) > 2:
                f.write(f'\n/-! Informal proof:\n{informal}\n-/\n')
            f.close()
        print(f'第{i + 1}个下载完成')
        sleep(0.5)
        


