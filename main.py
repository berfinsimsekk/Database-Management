import random  # for demo test
import sys
import time
import json
import re
import math

PAGESIZE = 2000
PAGE_IN_A_FILE = 10

splits = 0
parent_splits = 0
fusions = 0
parent_fusions = 0

bTrees = {}



class Node(object):
    """Base node object. It should be index node
    Each node stores keys and children.
    Attributes:
        parent
    """

    def __init__(self, parent=None):
        """Child nodes are stored in values. Parent nodes simply act as a medium to traverse the tree.
        :type parent: Node"""
        self.keys: list = []
        self.values: list[Node] = []
        self.parent: Node = parent

    def getAddress(self, x):

        index = 0

        for i in self.keys:
            if i == x:
                adr = self.values[index]
                return adr
            index = index+1

    def index(self, key):
        """Return the index where the key should be.
        :type key: str
        """
        for i, item in enumerate(self.keys):
            if key < item:
                return i

        return len(self.keys)

    def __getitem__(self, item):
        return self.values[self.index(item)]

    def __setitem__(self, key, value):
        i = self.index(key)
        self.keys[i:i] = [key]
        self.values.pop(i)
        self.values[i:i] = value

    def split(self):
        """Splits the node into two and stores them as child nodes.
        extract a pivot from the child to be inserted into the keys of the parent.
        @:return key and two children
        """
        global splits, parent_splits
        splits += 1
        parent_splits += 1

        left = Node(self.parent)

        mid = len(self.keys) // 2

        left.keys = self.keys[:mid]
        left.values = self.values[:mid + 1]
        for child in left.values:
            child.parent = left

        key = self.keys[mid]
        self.keys = self.keys[mid + 1:]
        self.values = self.values[mid + 1:]

        return key, [left, self]

    def __delitem__(self, key):
        i = self.index(key)
        del self.values[i]
        if i < len(self.keys):
            del self.keys[i]
        else:
            del self.keys[i - 1]

    def fusion(self):
        global fusions, parent_fusions
        fusions += 1
        parent_fusions += 1

        index = self.parent.index(self.keys[0])
        # merge this node with the next node
        if index < len(self.parent.keys):
            next_node: Node = self.parent.values[index + 1]
            next_node.keys[0:0] = self.keys + [self.parent.keys[index]]
            for child in self.values:
                child.parent = next_node
            next_node.values[0:0] = self.values
        else:  # If self is the last node, merge with prev
            prev: Node = self.parent.values[-2]
            prev.keys += [self.parent.keys[-1]] + self.keys
            for child in self.values:
                child.parent = prev
            prev.values += self.values

    def borrow_key(self, minimum: int):
        index = self.parent.index(self.keys[0])
        if index < len(self.parent.keys):
            next_node: Node = self.parent.values[index + 1]
            if len(next_node.keys) > minimum:
                self.keys += [self.parent.keys[index]]

                borrow_node = next_node.values.pop(0)
                borrow_node.parent = self
                self.values += [borrow_node]
                self.parent.keys[index] = next_node.keys.pop(0)
                return True
        elif index != 0:
            prev: Node = self.parent.values[index - 1]
            if len(prev.keys) > minimum:
                self.keys[0:0] = [self.parent.keys[index - 1]]

                borrow_node = prev.values.pop()
                borrow_node.parent = self
                self.values[0:0] = [borrow_node]
                self.parent.keys[index - 1] = prev.keys.pop()
                return True

        return False


class Leaf(Node):
    def __init__(self, parent=None, prev_node=None, next_node=None):
        """
        Create a new leaf in the leaf link
        :type prev_node: Leaf
        :type next_node: Leaf
        """
        super(Leaf, self).__init__(parent)
        self.next: Leaf = next_node
        if next_node is not None:
            next_node.prev = self
        self.prev: Leaf = prev_node
        if prev_node is not None:
            prev_node.next = self

    def __getitem__(self, item):
        return self.values[self.keys.index(item)]

    def __setitem__(self, key, value):
        i = self.index(key)
        if key not in self.keys:
            self.keys[i:i] = [key]
            self.values[i:i] = [value]
        else:
            self.values[i - 1] = value

    def split(self):
        global splits
        splits += 1

        left = Leaf(self.parent, self.prev, self)
        mid = len(self.keys) // 2

        left.keys = self.keys[:mid]
        left.values = self.values[:mid]

        self.keys: list = self.keys[mid:]
        self.values: list = self.values[mid:]

        # When the leaf node is split, set the parent key to the left-most key of the right child node.
        return self.keys[0], [left, self]

    def __delitem__(self, key):
        i = self.keys.index(key)
        del self.keys[i]
        del self.values[i]

    def fusion(self):
        global fusions
        fusions += 1

        if self.next is not None and self.next.parent == self.parent:
            self.next.keys[0:0] = self.keys
            self.next.values[0:0] = self.values
        else:
            self.prev.keys += self.keys
            self.prev.values += self.values

        if self.next is not None:
            self.next.prev = self.prev
        if self.prev is not None:
            self.prev.next = self.next

    def borrow_key(self, minimum: int):
        index = self.parent.index(self.keys[0])
        if index < len(self.parent.keys) and len(self.next.keys) > minimum:
            self.keys += [self.next.keys.pop(0)]
            self.values += [self.next.values.pop(0)]
            self.parent.keys[index] = self.next.keys[0]
            return True
        elif index != 0 and len(self.prev.keys) > minimum:
            self.keys[0:0] = [self.prev.keys.pop()]
            self.values[0:0] = [self.prev.values.pop()]
            self.parent.keys[index - 1] = self.keys[0]
            return True

        return False


class BPlusTree(object):
    """B+ tree object, consisting of nodes.
    Nodes will automatically be split into two once it is full. When a split occurs, a key will
    'float' upwards and be inserted into the parent node to act as a pivot.
    Attributes:
        maximum (int): The maximum number of keys each node can hold.
    """
    root: Node

    def __init__(self, maximum=4):
        self.root = Leaf()
        self.maximum: int = maximum if maximum > 2 else 2
        self.minimum: int = self.maximum // 2
        self.depth = 0

    def find(self, key) -> Leaf:
        """ find the leaf
        Returns:
            Leaf: the leaf which should have the key
        """
        node = self.root
        # Traverse tree until leaf node is reached.
        while type(node) is not Leaf:
            node = node[key]

        return node

    def __getitem__(self, item):
        return self.find(item)[item]

    def query(self, key):
        """Returns a value for a given key, and None if the key does not exist."""
        leaf = self.find(key)
        return leaf[key] if key in leaf.keys else None

    def change(self, key, value):
        """change the value
        Returns:
            (bool,Leaf): the leaf where the key is. return False if the key does not exist
        """
        leaf = self.find(key)
        if key not in leaf.keys:
            return False, leaf
        else:
            leaf[key] = value
            return True, leaf

    def __setitem__(self, key, value, leaf=None):
        """Inserts a key-value pair after traversing to a leaf node. If the leaf node is full, split
              the leaf node into two.
              """
        if leaf is None:
            leaf = self.find(key)
        leaf[key] = value
        if len(leaf.keys) > self.maximum:
            self.insert_index(*leaf.split())

    def insert(self, key, value):
        """
        Returns:
            (bool,Leaf): the leaf where the key is inserted. return False if already has same key
        """
        leaf = self.find(key)
        if key in leaf.keys:
            return False, leaf
        else:
            self.__setitem__(key, value, leaf)
            return True, leaf

    def insert_index(self, key, values: list[Node]):
        """For a parent and child node,
                    Insert the values from the child into the values of the parent."""
        parent = values[1].parent
        if parent is None:
            values[0].parent = values[1].parent = self.root = Node()
            self.depth += 1
            self.root.keys = [key]
            self.root.values = values
            return

        parent[key] = values
        # If the node is full, split the  node into two.
        if len(parent.keys) > self.maximum:
            self.insert_index(*parent.split())
        # Once a leaf node is split, it consists of a internal node and two leaf nodes.
        # These need to be re-inserted back into the tree.

    def delete(self, key, node: Node = None):
        if node is None:
            node = self.find(key)
        del node[key]

        if len(node.keys) < self.minimum:
            if node == self.root:
                if len(self.root.keys) == 0 and len(self.root.values) > 0:
                    self.root = self.root.values[0]
                    self.root.parent = None
                    self.depth -= 1
                return

            elif not node.borrow_key(self.minimum):
                node.fusion()
                self.delete(key, node.parent)
        # Change the left-most key in node
        # if i == 0:
        #     node = self
        #     while i == 0:
        #         if node.parent is None:
        #             if len(node.keys) > 0 and node.keys[0] == key:
        #                 node.keys[0] = self.keys[0]
        #             return
        #         node = node.parent
        #         i = node.index(key)
        #
        #     node.keys[i - 1] = self.keys[0]

    def show(self, node=None, file=None, _prefix="", _last=True):
        """Prints the keys at each level."""
        if node is None:
            node = self.root
        print(_prefix, "`- " if _last else "|- ", node.keys, sep="", file=file)
        _prefix += "   " if _last else "|  "

        if type(node) is Node:
            # Recursively print the key of child nodes (if these exist).
            for i, child in enumerate(node.values):
                _last = (i == len(node.values) - 1)
                self.show(child, file, _prefix, _last)

    def output(self):
        return splits, parent_splits, fusions, parent_fusions, self.depth

    def readfile(self, reader):
        i = 0
        for i, line in enumerate(reader):
            s = line.decode().split(maxsplit=1)
            self[s[0]] = s[1]
            if i % 1000 == 0:
                print('Insert ' + str(i) + 'items')
        return i + 1

    def leftmost_leaf(self) -> Leaf:
        node = self.root
        while type(node) is not Leaf:
            node = node.values[0]
        return node


def demo():
    bplustree = BPlusTree()
    #random_list = random.sample(range(1, 100), 20)
    random_list = [1,5,2,3,4,6,7,8]
    for i in random_list:
        bplustree[i] = 'test' + str(i)
        print('Insert ' + str(i))
        bplustree.show()

    random.shuffle(random_list)
    """
     for i in random_list:
        print('Delete ' + str(i))
        bplustree.delete(i)
        bplustree.show()
    """

   # print(bplustree.find(5).getAddress(5))



def createType(type_name, prim_key, fieldsAndTypes):

    print("GELDM")
    bplustree = BPlusTree()

    bTrees[type_name] = bplustree

    file = open("systemCatalog.csv", "a+")
    f = open(type_name+"1.txt", "w")

    file.write(type_name+","+str(fieldsAndTypes)+","+type_name+"1.txt"+"\n")

    nofFields = len(fieldsAndTypes)/2
    lengthOfARecord = int(nofFields * 20)
    #f.seek(0)


    nofRecords = math.floor(PAGESIZE / nofFields)


    text = (" " * lengthOfARecord) * nofRecords

    for page in range(PAGE_IN_A_FILE):
        print("")
        f.write("0")
        f.write(text)

    file.close()

    return True

def deleteType(type_name):
    
    del bTrees[type_name]

    file = open("systemCatalog.csv", "a+")

    #imdaaaaaaaaaaaat
    return True

def listType(outputFile):
    
    types = getAllTypeNames()

    for type in types:
        outputFile.write(type+"\n")

    return True

def createRecord(type_name, fields):

    systemCat = open("systemCatalog.csv")

    lines = systemCat.readlines()

    text = ""

    for line in lines:
        if line[0: len(type_name)] == type_name:
            text = line
            break

    #print(text,end="")
    fileName = text.split(',')[-1][:-1]

    #print(fileName,end="")

    f = open(fileName)
    f.seek(0)

    while f.read() != "0":
        f.seek(PAGESIZE)




    return True

def deleteRecord(type_name, prim_key):

    return True

def updateRecord(type_name, prim_key, fields):
    return True

def searchRecord(type_name, prim_key, outputFile):
    
    bTree = bTrees[type_name].find(prim_key).getAddress(prim_key)
    #gerisi yapılcak
    return True

def listRecord(type_name, outputFile):

    return True

def filterRecord(type_name, condition, outputFile):

    return True

def saveBTrees():

    
    type_names = getAllTypeNames()
    i = 0
    print(type_names)
    print(bTrees)
    #print(len(bTrees))
    #print(len(type_names))
    for bTree_name in bTrees:
        leaves = []
        values = []
        dic = {}
        bTree = bTrees[bTree_name]
        file = open("bTree"+type_names[i]+".txt", "w+")

        leftMost = bTree.leftmost_leaf()


        while leftMost is not None:
            leaves.extend(leftMost.keys)
            values.extend(leftMost.values) 
            leftMost =  leftMost.next      

        for j in range(len(leaves)):
            dic[leaves[j]] = values[j]

        file.write(str(json.dumps(dic)))

        i = i + 1

        file.close()


def getAllTypeNames():
    systemCat = open("systemCatalog.csv", "r")

    types = systemCat.readlines()
    types = types[1:]
    type_names = []

    for type in types:
        type_names.append(type.split(',')[0])

    return type_names

def createbTrees():

    type_names = getAllTypeNames()

    i = 0

    for type_name in type_names:

        file = open("bTree"+type_names[i]+".txt", "r+")

        bplustree = BPlusTree()

        text = file.read()

        dic = json.loads(text)

        for key in dic:
            bplustree.insert(key, dic[key])

        bTrees[type_name] = bplustree

        i = i + 1



if __name__ == '__main__':
    #demo()

    createbTrees()

    #print(len(bTrees))

    inputFileName = sys.argv[1]
    outputFileName = sys.argv[2]


    inputFile = open(inputFileName, 'r')
    outputFile = open(outputFileName, 'w')
    logFile = open('horadrimLog.csv','w+')

    lines = inputFile.readlines()

    for line in lines:
        words = line.split()


        if words[0].lower() == "create" and words[1].lower() == "type":
            type_name = words[2]
            nof_fields = int(words[3])
            prim_key_order = int(words[4])

            prim_key = words[3+2*prim_key_order]

            fieldsAndTypes = [None] * nof_fields*2

            for i in range(nof_fields*2):
                fieldsAndTypes[i] = words[5+i]

            success = createType(type_name, prim_key, fieldsAndTypes)


        if words[0].lower() == "delete" and words[1].lower() == "type":
            type_name = words[2]

            success = deleteType(type_name)

        if words[0].lower() == "list" and words[1].lower() == "type":

            success = listType(outputFile)

        if words[0].lower() == "create" and words[1].lower() == "record":
            type_name = words[2]
            fields = []

            for i in range(3,len(words)):
                fields.append(words[i])

            success = createRecord(type_name, fields)

        if words[0].lower() == "delete" and words[1].lower() == "record":
            type_name = words[2]
            prim_key = words[3]

            success = deleteRecord(type_name, prim_key)

        if words[0].lower() == "update" and words[1].lower() == "record":
            type_name = words[2]
            prim_key = words[3]
            fields = []

            for i in range(4,len(words)):
                fields.append(words[i])

            success = updateRecord(type_name, prim_key, fields)

        if words[0].lower() == "search" and words[1].lower() == "record":
            type_name = words[2]
            prim_key = words[3]

            success = searchRecord(type_name, prim_key, outputFile)

        if words[0].lower() == "list" and words[1].lower() == "record":
            type_name = words[2]

            success = listRecord(type_name, outputFile)

        if words[0].lower() == "filter" and words[1].lower() == "record":
            type_name = words[2]
            condition = words[3]

            success = filterRecord(type_name, condition, outputFile)


        if success:
            x = "success"
        else:
            x = "failure"

        logFile.write(str(int(time.time())) + "," + line + "," + x+"\n")

    
  
    """bplustree = BPlusTree()
    random_list = random.sample(range(1, 100), 20)
    random_list = ["a", "b", "c"]
    for i in random_list:
        bplustree[i] = 'test' + str(i)
        print('Insert ' + str(i))
        bplustree.show()

    bTrees["Angel"] = bplustree"""

    #print(bTrees['Angel'].find("5").keys)

    saveBTrees()

    outputFile.close()
    inputFile.close()



