import re
assembly_content = None
with open('assembly', 'r') as file:
    assembly_content = file.readlines()

for i in range(len(assembly_content)):
     assembly_content[i] = assembly_content[i].replace('.data', '')
     assembly_content[i] = assembly_content[i].replace('.code', '')
     assembly_content[i] = assembly_content[i].replace('...', '')
     assembly_content[i] = assembly_content[i].replace('0:', '')
     assembly_content[i] = assembly_content[i].replace('struct', '')
     assembly_content[i] = assembly_content[i].split('			')[0]
    # assembly_content[i] = assembly_content[i].split('   ')[0]

for i, line in enumerate(assembly_content):
    if len(line.strip()) < 2:
        assembly_content.remove(assembly_content[i])

toReplaceList = []
for number in range(100):
    toFind = 'PUSH [tag] {}'.format(number)
    lineNumber = -1
    tagIndex = -1
    for i, line in enumerate(assembly_content):
        if assembly_content[i].strip() == toFind:
            lineNumber = i
            toFindIndexTag = 'tag {}'.format(number)
            for j in range(i, len(assembly_content)):
                if assembly_content[j].strip() == toFindIndexTag:
                    tagIndex = j
                    #print("TAG INDEX: ", j)
                    toReplaceList.append((number, lineNumber, tagIndex + 1))
                    break


print(toReplaceList)
# toReplaceList = sorted(toReplaceList, key=lambda x: x[1])
counter = 0
for tagNumber, callLineNumber, tagLineIndex in toReplaceList:
    assembly_content[callLineNumber] = assembly_content[callLineNumber].strip().split(' ')[0] + ' ' + str(tagLineIndex - counter)
    counter += 1

counter = 0
for tagNumber, callLineNumber, tagLineIndex in toReplaceList:
    print(assembly_content[tagLineIndex-1-counter])
    assembly_content.remove(assembly_content[tagLineIndex-1-counter])
    counter += 1



bytecode = ''
for i, line in enumerate(assembly_content):
    # if line.strip() != '':
        bytecode += line.strip() + ' :: '
        print(i + 1, line.strip())

bytecode += 'nil'
# print(bytecode)
