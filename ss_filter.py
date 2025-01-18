file_path = "./result.txt"
out = "result_ss.txt"
sinkList = [
    "<org.apache.commons.collections.functors.InvokerTransformer: java.lang.Object transform(java.lang.Object)>" # or comment this line
]

gcs = []
ssSet = []
with open(file_path, 'r') as file:
    gc = []
    for line in file:
        if line == "\n":
            tempSink = gc[len(gc) - 1].rstrip()
            for gadget in gc:
                for sink in sinkList:
                    if sink in gadget:
                        tempSink = sink
                        break
            ss = gc[0].split("->")[0] + tempSink
            if ss not in ssSet:
                ssSet.append(ss)
                gcs.append(gc)
            gc = []
        else:
            gc.append(line)

with open(out, 'w') as fileout:
    for gc in gcs:
        for gadget in gc:
            fileout.write(gadget)
        fileout.write("\n")
    fileout.write("total gc count: " + str(len(gcs)))
