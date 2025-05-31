######### if-elif-else #########

#s: str
#v: [x]
#p: {"green", "yellow", "red"}
x = "yellow"
if x == "green":
    x = "yellow"
elif x == "yellow":
    x = "red"
else:
    x = "green"

#s: int
#v: [x]
x = 10
if x > 1:
    x = x + 1
elif x < -1:
    x = x - 1
else:
    x = 0

######### for-loop #########

#s: int
#v: [y]
y = 0
for i in range(10):
    y = y + i

#s: int
#v: [y, items]
y = 0
items = [1, 2, 3, 4, 5]
for i in items:
    y = y + i

#s: str
#v: [y, items]
y = ""
items = ["a", "b", "c", "d", "e"]
for i in items:
    y = y + i

######### while-loop #########

#s: int
#v: [z]
z = 0
while z < 10:
    z = z + 1

#s: str
#v: [z, count]
z = ""
count = 0
while count < 10:
    z = z + "a"
    count = count + 1