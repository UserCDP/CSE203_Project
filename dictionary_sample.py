class LetterTree:
    def __init__(self, value=None):
        self.value = value
        self.definition = None
        self.children = {}

    def __repr__(self) -> str:
        # represent the tree with branches between the nodes on different levels
        return f"Value: {self.value}, Children: {self.children}"

    
    def add(self, word, definition=None):
        if word == '':
            self.value = word
        if len(word) == 1:
            if word not in self.children:
                self.children[word] = LetterTree(word)
            self.children[word].definition = definition
        else:
            first = word[0]
            rest = word[1:]
            if first not in self.children:
                self.children[first] = LetterTree(first)
            self.children[first].add(rest, definition)

    def print_tree(self, level=0):
        if self.value is not None:
            if level > 0:
                prefix = '  ' * (level - 1) + '└── '
            else:
                prefix = ''
            print(prefix + str(self.value), end='')
            if self.definition is not None:
                print(f" (:{self.definition})")
            else:
                print()
        for i, child_key in enumerate(self.children.keys()):
            child = self.children[child_key]
            # if i < len(self.children) - 1:
            #     child.print_tree(level + 1)
            # else:
            child.print_tree(level + 1)

# class Forest:
#     def __init__(self):
#         self.trees = {}
    
#     def add(self, word, definition=None):
#         if word == '':
#             return
        # if len(word) == 1:
        #     if word not in self.trees:
        #         self.trees[word] = LetterTree(word)

    #         return
    #     first = word[0]
    #     rest = word[1:]
    #     if first not in self.trees:
    #         self.trees[first] = LetterTree(first, definition)
    #     self.trees[first].add(rest, definition)
    
    # def contains(self, word):
    #     if word == '':
    #         return True
    #     first = word[0]
    #     rest = word[1:]
    #     if first not in self.trees:
    #         return False
    #     return self.trees[first].contains(rest)
    

    

tree = LetterTree()

# Add words to the tree
words = {"apple": "a weird fruit",
         "bear": "A big animal",
         "ape": "A smaller animal",
         "bat": "Flying rat",
         "ball": "Round object"}
for word in words:
    tree.add(word, words[word])

# Print the tree structure
tree.print_tree()