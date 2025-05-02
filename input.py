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
#v: [y, items]
y = 0
items = [1, 2, 3, 4, 5]
for i in items:
    y = y + i

#s: str
#v: [z]
z = ""
while z < 10:
    z = z + "a"