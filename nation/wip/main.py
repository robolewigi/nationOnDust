import sys
import tty
import termios 
import os
import time
import random
import math
from pynput import keyboard
import traceback
import threading

#def: fg(c) bg(c) cursorVisible() windowText(set) createMap(set, val) graphics() draw(y) commands() onPress(key) onRelease(key) begin() gameLoop()
fd = sys.stdin.fileno()
oldSettings= termios.tcgetattr(fd)
tty.setraw(fd)
reset = "\033[0m"
colors= [[0,111,0], [55,55,0], [11,33,155], [11,33,55], [45,55,66], [11,66,33], [177,177,177], [111,99,44]] #0-grass 1-dirt 2-water 3-sky 4-mountain 5-mou/grass 6-snow 7-sand
focuses= ["NORmal","HUNter","SOLdier","GOVernor", "MINer"]
grades= ['F','D','C','B','A']
advNames=[["farming", "writing", "markets", "corporations"], ["spear", "army", "goverments", "wheel/animalFarming"], ["clothing", "music", "theater", "mission"], ["burial", "mound", "caste", "vassalage"]] #0-yellow 1-red 2-black 3-white 

current_keys = set()
class variables():
 listener= None
 running= 0 #0-run 1-stop 2-quit
 debug= 0
 buffer=[] #0- previous 1- current
 xy=[0,0]
 consoleOn= 0
 mapScroll=0
 windowState=-1 #(-1)-none 0-help 1-units 2-resources 3-internal 4-diplomacy
 history=[0, ["h"]]
 region=[] #0-green 1- mountain 2- shore
 mapSize=850
 map=[]
 resources=[] #(-1)-None 0-grove 1-fish 2-feathers 3-hides 4-trees 5-stone/flint 6-copper
 fpsTime = time.time()
 pictures=[]
 options=[0,20,1]#0-pictures 1-gameTime 2-difficulty
 regionWidth= 33
 #game
 units=[]
 investments=[]
 authorities=[]
 advancements=[1]*4 
v= variables()

class unit:
 focus=0 #0-normal 1-hunter 2-soldier 3-governer 4-miner
 grade=0 #0-f 1-d 2-c 4-b 5-a
 def __init__(self, l=[0,0]): self.loc=l

class authority:
 stock=[0]*7
 units=[]

class investment:
 def __init__(self, dem=[0,0,0], ti=[0,15], adv=1):
  self.demands=dem #0-bushels 1-copper 2-units
  self.time=ti
  advancement=adv

def bg(c): return f"\033[48;2;{c[0]};{c[1]};{c[2]}m"
def fg(c): return f"\033[38;2;{c[0]};{c[1]};{c[2]}m"
def cursorVisible(): print('\033[?25l' if v.consoleOn==0 else '\033[?25h', end='', flush=True)
def windowText(set=0): #0-help 1-units 2-resources 3-social
 if set==0: return ["controls:", "'ad' enter upDown", "command+ AliAses:", "'Help' 'CLearS'", "'Pause' 'new' 'Units'"
, "'Resources'", "'Social'", "'Units (#) (command)'" "options:",f"'pictures'= {v.options[0]}", f"'gametime'= {v.options[1]}", f"'DIFFiculty'= {v.options[2]}"]
 elif set==1:
  allUnits=[]
  for i in range(len(v.units)):
   allUnits.append(f"{i}, {focuses[v.units[i].focus]}, {grades[v.units[i].grade]}, {abs(v.units[i].loc[0])//v.regionWidth}")
  advDeny=""
  for i in range(4):
   advDeny+= " "+fg([0,188,0])+ focuses[1:][i] if v.advancements[1]>i else " "+fg([222,0,0])+ focuses[1:][i]
  return ["examples:","'Units 1 HUNter'", "'Units 0'", " ".join(focuses[:1])+ advDeny[:23], advDeny[23:],"(id focus grade", "location):",*allUnits]
 elif set==2:
  totals=[0]*8
  for r in v.resources:
   totals[r[0]]+=1
  return ["current/total/harvest:", f"Bushels 0/{totals[0]}/0", f"fish(Bushels) 0/{totals[1]}/0", f"Feathers 0/{totals[2]}/0", f"Hides 0/{totals[3]}/0",
f"Wood 0/{totals[4]}/0", f"flint(Stone) 0/{totals[5]}/0", f"Copper 0/{totals[6]}/0"]
 elif set==3:
  return ["investments:","","authorities:",""]

def createMap(set=0, val=0): #0-create 1-graphics
 if set==0:
  v.units=[]
  v.map=[]
  n = v.mapSize//v.regionWidth
  points = [0]*n
  v.region = [0]*n
  v.resources = [0]*n
  rest = list(range(n))
  weights = [1.0, 1.0, 1.0]
  weights2 = [1.0, 1.4, 1.3, 1.0, 1.0, 1.0, 1.1]
  regionTypes = [[0,1],[2],[0],[0,1],[0,1],[1,2],[1]]
  resourceChance = [0.6,0.5,0.4,0.3,0.45,0.26,0.15]
  start = True

  for j in range(n):
   randI = random.randrange(len(rest))
   ri = rest[randI]
   loc = ri*v.regionWidth

   # assign region + height
   for i in range(3):
    if random.random() < weights[i]:
     if i==0 and start:
      v.units.append(unit([-loc, 2]))
      v.mapScroll = loc
      start = False
     weights[i] *= [0.93,0.88,0.88][i]
     points[ri] = random.randint([5,11,0][i],[8,15,2][i])
     v.region[ri] = i
     break
    if i==2:
     v.region[ri] = i
     points[ri] = random.randint(5,8)

   # assign resource
   valid = [i for i in range(6,-1,-1) if v.region[ri] in regionTypes[i]]
   placed = False
   for i in valid:
    if random.random() < weights2[i]:
     v.resources[ri] = [i, loc, 1]
     weights2[i] *= resourceChance[i]
     placed = True
     break
   if not placed:
    v.resources[ri] = [-1, loc, 1]

   del rest[randI]

  points[-1] = points[0]
  v.region[-1] = v.region[0]
  for i in range(v.mapSize):
   pos = i/v.mapSize*len(points)
   a = points[math.floor(pos)]
   b = points[min(len(points)-1, math.ceil(pos))]
   v.map.append(int(a+(pos%1)*(b-a)))

 elif set==1:
  mv, h = v.map[val[0]], val[1]
  if mv >= h:
   if v.region[min(len(v.region)-1, val[0]//v.regionWidth)]==2 and mv<4: return bg(colors[7])
   if mv>9: return bg(colors[[1,5,4,6][min(3, h>3)+(h>8)+(h>11)]])
   return bg(colors[0]) if mv>3 and h>2 else bg(colors[1])
  return bg(colors[2]) if h<4 else bg(colors[3])

def graphics():
 if v.running!=0: return
 wid = v.xy[0]//2 if v.windowState!=-1 else v.xy[0]
 hei = v.xy[1]-1
 buf = [[" "]*wid for _ in range(hei)]

 for y in range(hei):
  for x in range(wid):
   buf[hei-1-y][x] = createMap(1, [(x+v.mapScroll)%v.mapSize, y]) + " "

 newUnits= [[7, u.loc[0], u.loc[1]] for u in v.units]
 all= v.resources+ newUnits
 for re in all:
  if re[0]==-1: continue
  rLoc= (abs(re[1])- v.mapScroll)% v.mapSize
  if rLoc > v.mapSize - 16: rLoc -= v.mapSize
  if rLoc + 15 > 0 and rLoc < wid:
   try:
    if v.options[0]==0 or (v.options[0]==1 and re[0]==7):
     for p in v.pictures[re[0]]:
      center= -8 if re[0]==7 else 0
      px= 15-p[0]+rLoc+center if re[1]<0 else p[0]+rLoc+center
      if 0 <= px < wid and 0<=hei-1-p[1]<hei:
       buf[hei-p[1]-re[2]][px]= bg([p[2], p[3], p[4]])+ ' '
   except: pass
  if 0 <= rLoc < wid-1:
   buf[hei-re[2]][rLoc] = buf[hei-re[2]][rLoc][:-1]+ fg([255,255,255])+ ['b','b','f','h','w','s','c','U'][re[0]]
 
 if v.windowState!=-1:
  for y in range(hei):
   if y<len(windowText(v.windowState)):
    buf[y][-1]+=reset+ windowText(v.windowState)[y]
 for y in range(hei):
  v.buffer[1][y]= ''.join(buf[y])+ reset
 for y in range(v.xy[1]):
  draw(y)

def draw(y):
 if v.running!=0: return
 if v.buffer[0][y]== v.buffer[1][y]: return
 v.buffer[0][y]= v.buffer[1][y]
 print(f"\033[{y+1};1H", end="")
 print("\033[K", end="")
 print(v.buffer[1][y], end="")

def commands():
 c= v.buffer[1][v.xy[1]-1].lower()
 parts= c.split(" ")
 if c in ["h","help"]:
  if v.windowState!=0: v.windowState= 0
  else: v.windowState=-1
 if c in ["clear","clears","cls"]:
  v.windowState=-1
 elif parts[0] in ["units", "u"]:
  if len(parts)>1:
   if parts[1].isdigit():
    try:
     if len(parts)==2:
      v.mapScroll= abs(v.units[int(parts[1])].loc[0])
     elif len(parts)==3:
      combind= focuses+ ["nor", "hun", "sol", "gov", "min"]
      if parts[2] in combind:
       idx= combind.index(parts[2])%5
       if v.advancements[1]> idx-1:
        v.units[int(parts[1])].focus= idx
    except: pass  
   
  else:
   if v.windowState!=1: v.windowState=1
   else: v.windowState=-1
 elif c in ["resources", "r"]:
  if v.windowState!=2: v.windowState=2
  else: v.windowState=-1
 elif c in ["social", "s"]:
  if v.windowState!=3: v.windowState=3
  else: v.windowState=-1

 elif c in ["pictures"]:
  v.options[0]= (v.options[0]+1)%3
 elif len(parts)==2:
  if parts[1].isdigit():
   if parts[0] in ["gametime"]:
    v.options[1]= int(parts[1])
   elif parts[0] in ["difficulty", "diff"]:
    v.options[2]= int(parts[1])
 elif c in ["pause","p"]:
  v.running=1
 elif c in ["new"]:
  createMap()
 elif c=="":
  v.windowState=-1
 graphics()

def onPress(key):
 try:
  current_keys.add(key) 
  if key == keyboard.Key.enter:
   if v.running==1: tty.setraw(fd); v.running=0; graphics(); return
   if v.consoleOn==0:
    v.consoleOn= 1
    v.buffer[1][v.xy[1]-1]=""
   else:
    v.consoleOn=0
    commands()
    v.history[0]=0
    if v.buffer[1][-1]!= "" and v.buffer[1][-1]!= v.history[1][0]:
     v.history[1].insert(0, v.buffer[1][-1])
     v.history[1]= v.history[1][:11]
    v.buffer[1][-1]="enter+ 'h'+ enter"
  if key == keyboard.Key.up or key == keyboard.Key.down:
   if v.consoleOn!=1: v.consoleOn= 1
   else:
    if key == keyboard.Key.up: v.history[0]= min(min(10,len(v.history[1])-1), v.history[0]+1)
    else: v.history[0]= v.history[0]= max(0, v.history[0]-1)
   v.buffer[1][-1]= v.history[1][min(len(v.history[1])-1, v.history[0])]

  cursorVisible()
  if v.consoleOn== 1:
   if key == keyboard.Key.backspace:
    v.buffer[1][v.xy[1]-1]= v.buffer[1][v.xy[1]-1][:-1]
   if key == keyboard.Key.space:
    v.buffer[1][v.xy[1]-1]+= " "
   if hasattr(key, 'char') and key.char:
    if key.char.isprintable():
     v.buffer[1][v.xy[1]-1]+= key.char
   v.buffer[1][v.xy[1]-1]=v.buffer[1][v.xy[1]-1][-v.xy[0]:] 
  else:
   if hasattr(key, 'char') and key.char:
    if key.char.lower() == 'a':
     v.mapScroll= int(v.mapScroll-v.xy[0]/10)% v.mapSize
    elif key.char.lower() == 'd':
     v.mapScroll= int(v.mapScroll+v.xy[0]/10)% v.mapSize
    if key.char.lower() in ['a','d']: graphics()
  draw(v.xy[1]-1)

  if isinstance(key, keyboard.KeyCode):
   if (keyboard.Key.ctrl_l in current_keys or keyboard.Key.ctrl_r in current_keys) and key.char in ['d','c']:
    v.running=2 
 except:
  v.running=1
  traceback.print_exc()
  termios.tcsetattr(fd, termios.TCSADRAIN, oldSettings)

def onRelease(key):	
 try: current_keys.remove(key)
 except KeyError: pass

def begin():
 createMap()
 cursorVisible()
 try:
  names= ["bush.txt", "fish.txt", "turkey.txt", "deer.txt", "tree.txt", "stone.txt", "copper.txt", "human.txt"]
  for i in range(len(names)):
   with open(os.path.dirname(os.path.abspath(__file__))+"/img/"+names[i], 'r') as file:
    data = eval(f'[{file.read()}]')
    newList=[]
    for idx in data[1:]:
     newList.append([int(idx[0])%16,int(idx[0])//16, int(idx[1])//(256*256), int(idx[1])//256%256, int(idx[1])%256])
    maxY = max(p[1] for p in newList)
    for p in newList:
     p[1] = maxY - p[1]
    v.pictures.append(newList)
 except Exception as e:
  print("error in (location)/img")
  v.running=1

def gameLoop():
 while True:
  threading.Event().wait(v.options[1])
    

begin()
v.listener = keyboard.Listener(on_press=onPress, on_release=onRelease)
v.listener.start()
threading.Thread(target=gameLoop, daemon=True).start()
while v.running!=2:
 try:
  size = os.get_terminal_size()
  if v.xy!=[size.columns,size.lines]:
   if [size.columns, size.lines]==[0,0]: continue
   v.xy=[size.columns, size.lines]
   v.buffer=[[""]* v.xy[1], [""]* v.xy[1]]
   v.buffer[1][v.xy[1]-1]="enter+ 'h'+ enter"
   graphics()
  
  newDebug= '' if v.debug== 0 else str(v.debug)
  pauseText=newDebug if v.running== 0 else "!P!"+newDebug
  pauseText= "" if pauseText=="" else pauseText+"-"
  print(f"\033]0;{pauseText}nationOnDust{(1 / (time.time() - v.fpsTime)):.1f}\007", end='', flush=True)
  v.fpsTime = time.time()
  time.sleep(0.001)
 except Exception as e:
  v.running=1
  termios.tcsetattr(fd, termios.TCSADRAIN, oldSettings)
  traceback.print_exc()

v.listener.stop()
termios.tcsetattr(fd, termios.TCSADRAIN, oldSettings)