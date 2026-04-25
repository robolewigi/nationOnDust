import sys
import tty
import termios 
import os
import time
import random
import math
import traceback
import threading

fd = sys.stdin.fileno()
oldSettings= termios.tcgetattr(fd)
tty.setraw(fd)
reset = "\033[0m"
colors= [[0,111,0], [55,55,0], [11,33,155], [11,33,55], [45,55,66], [11,66,33], [177,177,177], [111,99,44]] #0-grass 1-dirt 2-water 3-sky 4-mountain 5-mou/grass 6-snow 7-sand
focuses= ["NORmal", "FORager","HUNter","SOLdier","GOVernor", "MINer"]
grades= ['F','D','C','B','A']
advNames=[["farming", "writing", "markets", "corporations"], ["spear", "army", "goverments", "wheel/animalFarming"], ["clothing", "music", "theater", "mission"], ["burial", "mound", "caste", "vassalage"]] #0-yellow 1-red 2-black 3-white
polNames=["urbanSprawl", "policeState", "quarantine", "divineRight"]
buildNames=["farm", "camp", "lodge", "mound"]
eventNames=["unitMigration", "mobilize", "disease", "moundCreate"]
resourceNames=["Bushels","Feathers", "Hides", "Wood", "flint(S)", "Copper"]
pictureNames= ["bush.txt","fish.txt","turkey.txt","deer.txt", "tree.txt","stone.txt","copper.txt","human.txt", "humanFlip.txt","hut.txt","fire.txt","weak.txt", "farm.txt","camp.txt","lodge.txt","mound.txt"]
current_keys = set()

class variables():
 def __init__(self):
  self.listener= None
  self.running= 0 #0-run 1-stop 2-quit
  self.buffer=[] #0- previous 1- current
  self.xy=[0,0]
  self.consoleOn= 0
  self.windowState=-1 #(-1)-none 0-help 1-units 2-resources 3-internal 4-diplomacy
  self.history=[0, ["h"]]
  self.fpsTime = time.time()
  self.pictures=[]
  self.options=[0,500,1, 0] #0-pictures 1-gameSpeed 2-difficulty 3-windowSize
  self.status=""
  self.console=""
  self.debug= [None, True]
  self.consoleScroll= 0
v= variables()

class region():
 def __init__(self):
  self.loc= -1
  self.type= 0 #0-green 1- mountain 2- shore
  self.resource= -1 #(-1)-None 0-grove 1-fish 2-feathers 3-hides 4-trees 5-stone/flint 6-copper
  self.claimed= False
  self.building= -1
 def to_dict(self): return {'loc':self.loc,'type':self.type,'resource':self.resource,'building':self.building,'claimed':self.claimed}
 @classmethod
 def from_dict(cls, d): r=cls(); r.__dict__.update(d); return r

class unit():
 def __init__(self, lo=[0,0]):
  self.loc= lo
  self.focus=0 #0-normal 1-hunter 2-soldier 3-governer 4-miner
  self.grade=0 #0-f 1-d 2-c 4-b 5-a
  self.flipped= True
  self.goto= lo[0]
  self.prepare= -1
  self.power= 1
  self.broken= 0
  self.weak= 0
  self.loyalty= 100
 def to_dict(self): return {'loc':self.loc,'focus':self.focus,'grade':self.grade,'flipped':self.flipped,'goto':self.goto,'prepare':self.prepare,'power':self.power,'broken':self.broken,'weak':self.weak,'loayalty':self.loayalty}
 @classmethod
 def from_dict(cls, d): u=cls(); u.__dict__.update(d); return u

class authority():
 def __init__(self, lo=[0,0]):
  self.level= 1 
  self.loc=lo
  self.claims=[]
  self.threats= []
  self.health= 100
 def to_dict(self): return {'level':self.level,'loc':self.loc,'claims':self.claims,'threats':self.threats,'health':self.health}
 @classmethod
 def from_dict(cls, d): a=cls(); a.__dict__.update(d); return a

class investment(): #0;3-yel 4;7-red 8;11-bla 12;15-whi 16;19-policies 20;23-build 24;27-events
 def __init__(self, ty):
  self.type=ty
  self.current= 0
  self.enabled= False
  self.time= [25,30,33,40, 25,30,33,40, 25,30,33,40, 25,30,33,40, -1,-1,-1,-1, 30,30,30,30, 0,0,0,0][ty]
  self.amount= [2,2,3,5, 2,2,3,5, 2,2,3,5, 2,2,3,5, 3,3,3,3, 5,5,5,5, 0,0,0,0][ty]
  self.resource= [2,2,2,2, 5,5,5,5, 3,3,3,3, 4,4,4,4, 1,1,1,1, 5,5,5,5, -1,-1,-1,-1][ty] #0-bus fea hid woo fli 5-cop
  self.value= 0
 def to_dict(self): return {'type':self.type,'time':self.time,'amount':self.amount,'resource':self.resource}
 @classmethod
 def from_dict(cls, d): inv=cls(); inv.__dict__.update(d); return inv

class world:
 def __init__(self):
  self.mapSize=850
  self.map=[]
  self.regions=[]
  self.regionWidth= 33

  self.units=[]
  self.auths=[]

  self.delay= 1

w= world()

class player:
 def __init__(self):
  self.unitNums= [] 
  self.mapScroll= 0
  self.save="a"
  self.homeLocation= 0

  self.storage= [2]*6 #0-bushels feathers hides wood flint copper
  self.profits= [0]*6 #0-bushels feathers hides wood flint copper
  self.profits[0]= 4

  self.advancements= [1]*4
  self.investments= []
  self.goals= []
  self.goalIdx= 0
  self.goalPass= False
  self.lost= False
  self.apoptosis= 0
  
p= player() 

def bg(c): return f"\033[48;2;{c[0]};{c[1]};{c[2]}m"
def fg(c): return f"\033[38;2;{c[0]};{c[1]};{c[2]}m"
def cursorVisible(): print('\033[?25l' if v.consoleOn==0 else '\033[?25h', end='', flush=True)


def windowText(set=0): #0-help 1-unit 2-resource 3-social
 if set==0: return ["controls:", "'ad' enter upDown 'qe'", "command+ AliAses:", "'Help' 'CLearS'", "'Pause' 'new' 'save'", "'save (name)' 'load (name)'", "'Unit' 'Resource'", "'Social'", "LOcation #" "options:",f"'PICtures'= {v.options[0]}", f"'GAmeSpeed'= {v.options[1]}", f"'DIFFiculty'= {v.options[2]}", f"'save'= '{p.save}'", f"'WINdowSize'= {v.options[3]}", "", "'HOMelocation (loc);","'Unit (id) (focus)'", "'Unit (id) AUthority (Au id)'", "'Unit (id) MITosis'", "'Unit (id) aPOPtosis'","'AUthority (id) ATTack'", "MIGrate", "INvestment (id)"]

 elif set==1:
  allUnits=[]
  for un in p.unitNums:
   if w.units[un] is None: continue
   allUnits.append(f"{un} {focuses[w.units[un].focus]} {grades[w.units[un].grade]} {abs(w.units[un].loc[0])//w.regionWidth} {max(w.units[un].weak, w.units[un].broken)} {w.units[un].loyalty}")
  allTexts=["", ""]
  for i in range(6):
   colorFocus= fg([0,188,0]) if i<= p.advancements[1]+ 1 else fg([222,0,0])
   allTexts[min(1, i//3)]= allTexts[min(1, i//3)]+ colorFocus+ focuses[i]+ " "
  return ["examples:","'u 0/2 hunter'", *allTexts, "", "(id focus grade", "location stopped loyalty):",*allUnits]

 elif set==2:
  totals=[0]*8
  for r in [r for r in w.regions if r.resource != -1]:
   totals[r.resource] += 1
  allProfits= []
  for i in range(len(p.profits)):
   operator = "+" if p.profits[i] >= 0 else "-"
   allProfits.append(f"{resourceNames[i]}= {p.storage[i]}{operator} {abs(p.profits[i])}")
  return ["totals:", f"Bushels {totals[0]}", f"fish(Bushels) {totals[1]}", f"Feathers {totals[2]}", f"Hides {totals[3]}",
f"Wood {totals[4]}", f"flint(S) {totals[5]}", f"Copper {totals[6]}", "", "storage:", *allProfits]

 elif set==3:
  authText= []
  threatLevel= 0
  invText= []
  for i in range(len(p.investments)):
   newCol= fg([0,188,0]) if p.investments[i].enabled else fg([222,0,0])
   invText.append( f"{newCol}V {i}/{resourceNames[p.investments[i].resource]}/{p.investments[i].time}/{p.investments[i].current} V")
   invText.append(f"{investmentHelp(i, True)}")
  for i in range(len(w.auths)):
   for threat in w.auths[i].threats:
    threatLevel+= w.units[threat].power
   authText.append(f"{i} {w.auths[i].loc[0]// w.regionWidth} {w.auths[i].level} {threatLevel}")
  goalColor= fg([0,188,0]) if p.goalPass else fg([222,0,0])
  return ["V (id/res./amo./time/cur.) V", "investments:", *invText, "","authorities:", "(Id Loc Level threat)", *authText, "", "danger:", goalColor+ goalText(p.goals[p.goalIdx], p.goalIdx), f"{55- (w.delay% 55)}"]

def createMap(set=0, val=0): #0-create 1-view 2-migrate
 if set in [0,2]:
  if set==0:
   w.units= []
   p.unitNums=[]
   p.lost= False
   p.goalPass= False
   p.apoptosis= 0
   p.storage= [0]*6 
   v.status= ""
   for i in range(10):
    p.goals.append(random.randint(0,4))
   p.goals.append(5)
   p.goals.append(6)
  w.map=[]
  w.auths= []
  p.goals=[0]
  p.goalIdx= 0
  p.profits= [0]*6
  p.profits[0]= 100 if v.debug[1] else 4
  n = w.mapSize//w.regionWidth
  points = [0]*n
  w.regions = [region() for _ in range(n)]
  rest = list(range(n))
  weights = [1.0, 1.0, 1.0]
  weights2 = [1.0, 1.4, 1.3, 1.0, 1.0, 1.0, 1.1]
  regionTypes = [[0,1],[2],[0],[0,1],[0,1],[1,2],[1]]
  resourceChance = [0.6,0.5,0.4,0.3,0.45,0.26,0.15]
  start = 0

  for j in range(n):
   randI = random.randrange(len(rest))
   ri = rest[randI]
   loc = ri*w.regionWidth

   # assign region + height
   for i in range(3):
    if random.random() < weights[i]:
     weights[i] *= [0.93,0.88,0.88][i]
     points[ri] = random.randint([5,11,0][i],[8,15,2][i])
     w.regions[ri].type = i
     break
    if i==2:
     w.regions[ri].type = i
     points[ri] = random.randint(5,8)

   # assign resource
   valid = [i for i in range(6,-1,-1) if w.regions[ri].type in regionTypes[i]]
   placed = False
   for i in valid:
    if random.random() < weights2[i]:
     w.regions[ri].resource= i
     weights2[i] *= resourceChance[i]
     placed = True
     break
   if not placed:
    w.regions[ri].resource= -1
   w.regions[ri].loc= loc

   del rest[randI]

  points[-1] = points[0]
  w.regions[-1].type = w.regions[0].type
  for i in range(w.mapSize):
   pos = i/w.mapSize*len(points)
   a = points[math.floor(pos)]
   b = points[min(len(points)-1, math.ceil(pos))]
   w.map.append(int(a+(pos%1)*(b-a)))
  
  greenRegions = [r for r in w.regions if r.type == 0]
  chosen = random.sample(greenRegions, 2)
  if set== 0:
   newUnit(chosen[0].loc)
  p.homeLocation= chosen[0].loc + w.regionWidth//2
  p.mapScroll = chosen[0].loc
  newAuth(chosen[1].loc + w.regionWidth//2)

 elif set==1:
  mv, h = w.map[val[0]], val[1]
  if mv >= h:
   if w.regions[min(len(w.regions)-1, val[0]//w.regionWidth)].type==2 and mv<4: return bg(colors[7])
   if mv>9: return bg(colors[[1,5,4,6][min(3, h>3)+(h>8)+(h>11)]])
   return bg(colors[0]) if mv>3 and h>2 else bg(colors[1])
  return bg(colors[2]) if h<4 else bg(colors[3])

def graphics(r=None):
 wid = v.xy[0]//2- v.options[3] if v.windowState!=-1 else v.xy[0]
 hei = v.xy[1]-1
 if r is None: return
 if r== v.xy[1]-1:
  if v.consoleOn==1:
   v.buffer[1][-1]= v.console[-v.xy[0]:]
  else: v.buffer[1][-1]= v.status
  if v.debug[0] is not None and v.consoleOn==0:
   v.buffer[1][-1]= str(v.debug[0])[-v.xy[0]:]
 else:
  buf = [createMap(1, [(x+ p.mapScroll)%w.mapSize, hei-1-r])+ " " for x in range(wid)]
  items =( [[re.resource, re.loc, 1, int(re.claimed)] for re in w.regions if re.resource!= -1] 
  +[[reg.building+ 12, reg.loc+ w.regionWidth//2] for reg in w.regions if reg.building!= -1] 
  +[[10, p.homeLocation, 1]]
  +[[9, au.loc[0], au.loc[1]] for au in w.auths if au is not None]
  +[[(8 if un.flipped else 7) if un.weak== 0 else 11, un.loc[0], un.loc[1], un.broken>0] for un in w.units if un is not None])
  for re in items:
   if re[0]==-1: continue
   rLoc = (re[1]-p.mapScroll)%w.mapSize
   if rLoc > w.mapSize-16: rLoc -= w.mapSize
   isUnit = re[0] in [7,8]
   for pi in v.pictures[re[0]]:
    px = rLoc + pi[0]- 8
    if 0 <= px < wid and pi[1] == hei-re[2]-r:
     newCol= [pi[2],pi[3],pi[4]]
     if len(re)>3:
      if re[3]== 1:
       newCol= [pi[2]//4,pi[3]//4,pi[4]//4]
     buf[px] = bg(newCol) + ' '
   if 0 <= rLoc < wid and hei-re[2] == r and v.options[0] in [0,4]:
    buf[rLoc] = buf[rLoc][:-1] + fg([255,255,255]) + ['b','b','f','h','w','s','c','U','U', 'A', 'H', 'u'][re[0]]
  if v.windowState!=-1 and r < len(windowText(v.windowState))- v.consoleScroll:
   if v.windowState== 3: gameHelp(4)
   buf[-1]+= reset + windowText(v.windowState)[r+ v.consoleScroll]
  v.buffer[1][r] = ''.join(buf)+ reset

def draw():
 for y in range(v.xy[1]):
  if v.buffer[0][y]== v.buffer[1][y]: continue  
  v.buffer[0][y]= v.buffer[1][y]
  sys.stdout.write(f"\033[{y+1};1H\033[K{v.buffer[1][y]}")
 if v.console=="":
  sys.stdout.write(f"\033[{v.xy[1]};1H")
 sys.stdout.flush()

def inputLoop():
 while v.running!= 2:
  ch = sys.stdin.read(1)
  if ch == '\r' or ch == '\n': #enter
   if v.running==1:
    tty.setraw(fd);
   if v.consoleOn==0:
    v.consoleOn= 1
    v.console=""
   else:
    v.consoleOn=0
    commands()	
    v.history[0]=0
    if v.console!= "" and v.console!= v.history[1][0]:
     v.history[1].insert(0, v.console)
     v.history[1]= v.history[1][:11]
   cursorVisible()

  elif ch == '\x03' or ch == '\x04':  # ctrl+c / ctrl+d
   v.running=2 
  elif ch == '\x1b':                  # escape sequence
   seq = sys.stdin.read(2)
   if seq in ['[A','[B']:
    if v.consoleOn!=1: v.consoleOn= 1
    if seq == '[A': #up arrow
     v.history[0]= min(min(10,len(v.history[1])-1), v.history[0]+1)
    else:
     v.history[0]= max(0, v.history[0]-1)
    v.console= v.history[1][min(len(v.history[1])-1, v.history[0])]

  elif ch == '\x7f': #backspace
   v.console= v.console[:-1]
  elif ch.isprintable():
   v.console+= ch

  if v.consoleOn==0:
   if ch.lower()=='a':
    p.mapScroll= int(p.mapScroll-v.xy[0]/10)% w.mapSize
    for y in range(v.xy[1]): graphics(y)
   elif ch.lower()=='d':
    p.mapScroll= int(p.mapScroll+v.xy[0]/10)% w.mapSize
    for y in range(v.xy[1]): graphics(y)
   elif ch.lower()=='f':
    if v.debug[1]: gameLoop(False)
   elif ch.lower()=='g':
    if v.debug[1]: newUnit(p.mapScroll)
   elif ch.lower()=='h':
    if v.debug[1]: saveLoadGame(False, True)
  if v.windowState!=-1 and v.consoleOn!=1:
   if ch.lower() in ['q', 'e']:
    if ch.lower()=='q':
     v.consoleScroll= max(0, v.consoleScroll-1)
    else:
     v.consoleScroll+= 1
    for i in range(v.xy[1]-1): graphics(i)
   
  graphics(v.xy[1]-1)
  draw()

#!partGame
def commands():
 c= v.console.lower()
 saveOn= False
 parts= c.split(" ")
 numbers=[[],[]]
 if len(parts)>1:
  if parts[1].isdigit():
   numbers[0].append(int(parts[1]))
  elif "/" in parts[1]:
   try:
    numbers[0]= [int(part) for part in parts[1].split("/")]
   except: pass
 if len(parts)>3:
  if parts[3].isdigit(): 
   numbers[1].append(int(parts[3]))
  for i in range(2):
   for j in range(len(numbers[i])-1, -1, -1):
    if not isinstance(int(numbers[i][j]), int):
     del numbers[i][j]
    elif parts[i* 2] in ["units", "u"] and numbers[i][j]>= len(w.units):
     del numbers[i][j]
    elif parts[i* 2] in ["authority", "au"] and numbers[i][j]>= len(w.auths):
     del numbers[i][j]
    else:
     numbers[i][j]= int(numbers[i][j])

 if c in ["new"]: createMap()
 if p.lost: return

 if c in ["pause","p"]:
  if v.running==0:
   v.running=1
   v.status= "paused!"
  else:
   v.running= 0
   v.status=""

 elif c in ["h","help"]:
  if v.windowState!=0: v.windowState= 0
  else: v.windowState=-1
 elif c in ["clear","clears","cls"]:
  v.windowState=-1
 elif c in ["migrate", "mig"]:
  createMap(2)

 if len(numbers[0])>0:
  for num in numbers[0]:
   if len(parts)>2: 
    if parts[0] in ["authority", "au"]:
     if parts[2] in ["attack", "att"]:
      if len(w.auths)> num:
       if w.auths[num] is not None:
        authLoc= w.auths[num].loc[0]// w.regionWidth* w.regionWidth
        for uIdx in w.auths[num].threats:
         if w.units[uIdx] is not None:
          if w.units[uIdx].broken+ w.units[uIdx].weak== 0:
           w.units[uIdx].goto= random.randint(authLoc, authLoc+ w.regionWidth)

    if parts[0] in ["unit", "u"]:
     if len(w.units)> num:
      combind= focuses+ ["nor", "for", "hun", "sol", "gov", "min"]
      if parts[2] in combind:
       idx= combind.index(parts[2])%(len(focuses)//2)
       if p.advancements[1]> idx-2:
        if w.units[num] is not None:
         if w.units[num].weak+ w.units[num].broken== 0:
          w.units[num].focus= idx

      elif parts[2] in ["apoptosis", "pop"]:
       if w.units[num] is not None:
        if w.units[num].broken+ w.units[num].weak== 0:
         p.apoptosis+= 1
         w.units[p.unitNums[num]]= None
         del p.unitNums[num]

      elif parts[2] in ["mitosis", "mit"]:
       if w.units[num] is not None:
        if w.units[num].broken+ w.units[num].weak==0:
         newUnit(w.units[num].loc[0])
         w.units[num].broken= 28
         w.units[-1].weak= 32
         w.units[-1].loyalty=50

   if len(numbers[1])>0:
    if len(parts)>2:
     if parts[2] in ["authority", "au"] and parts[0] in ["unit", "u"]:
      if w.auths[numbers[1][0]] is not None and w.units[num] is not None:
       if w.units[num].weak+ w.units[num].broken== 0:
        if w.units[num].prepare== numbers[1][0]:
         w.units[num].prepare= -1
         if num in w.auths[numbers[1][0]].threats:
          w.auths[numbers[1][0]].threats.remove(num)
          
        else:
         w.units[num].prepare= numbers[1][0]
         homeLoc= (p.homeLocation// w.regionWidth)* w.regionWidth
         w.units[num].goto= random.randint(homeLoc,homeLoc+ w.regionWidth) 

   if parts[0] in ["investment", "in"]:
    if len(p.investments)> num:
     p.investments[num].enabled= not p.investments[num].enabled
     if p.investments[num].type in [16,17,18,19] and not p.investments[num].enabled:
      p.investments[num].enabled= not p.investments[num].enabled
     if p.investments[num].type in [20,21,22,23] and p.investments[num].enabled:
      p.investments[num].value= p.homeLocation// w.regionWidth

   if parts[0] in ["homelocation", "hom"]:
    p.homeLocation= min(w.mapSize, num* w.regionWidth+ w.regionWidth//2)

   elif parts[0] in ["location", "lo"]:
    p.mapScroll= min(w.mapSize ,int(num)* w.regionWidth)

   if parts[0] in ["gamespeed", "gas"]:
    v.options[1]= num
    saveOn= True
   elif parts[0] in ["difficulty", "diff"]:
    v.options[2]= num
    saveOn= True
   elif parts[0] in ["windowsize", "wins"]:
    v.options[3]= num

 if c in ["unit", "u"]:
  if v.windowState!=1: v.windowState=1
  else: v.windowState=-1
 elif c in ["resources", "r"]:
  if v.windowState!=2: v.windowState=2
  else: v.windowState=-1
 elif c in ["social", "s"]:
  if v.windowState!=3: v.windowState=3
  else: v.windowState=-1

 elif c in ["pictures", "pic"]:
  v.options[0]= (v.options[0]+1)%5
  saveOn= True
 elif len(parts)==2:
  if parts[0] in ["load"]:
   p.save= parts[1]
   saveLoadGame(True)
  elif parts[0] in ["save"]:
   p.save= parts[1]
   saveLoadGame()
  
 if c in ["save"]:
  saveLoadGame()
 elif c=="":
  v.windowState=-1
 for y in range(v.xy[1]): graphics(y); 
 if saveOn: saveLoad()
   
def saveLoad(load= False):
 opt = ['pictures', 'gameSpeed', 'difficulty', 'gameName', 'windowSize']
 if not load:
  with open('settings.txt', 'w') as filehandle:
   for i in range(len(v.options)):
    filehandle.write(f'{opt[i]}= {v.options[i]}\n')
 else:
  if os.path.exists('settings.txt'):
   with open('settings.txt', 'r') as filehandle:
    lines = filehandle.readlines()
    for i in range(len(lines)):
     v.options[i]= int(lines[i].split('=')[1].strip())

def saveLoadGame(load= False, deb= False):
 skip = {'regions','units','auths', 'investments'}
 if not load or deb:
  if deb: os.makedirs('saves', exist_ok=True)
  with open(f"saves/{p.save}.txt" if not deb else "deb.txt", 'w') as f:
   for name, value in vars(w).items():
    if name in skip: continue
    f.write(f"{name}={repr(value)}\n")
   f.write(f"regions={[r.to_dict() for r in w.regions]}\n")
   f.write(f"units={[u.to_dict() if u is not None else None for u in w.units]}\n")
   f.write(f"auths={[a.to_dict() if a is not None else None for a in w.auths]}\n")
   f.write(f"investments={[inv.to_dict() for inv in p.investments]}\n")
   f.write("\n")
   for name, value in vars(p).items():
    f.write(f"{name}={repr(value)}\n")
   if deb:
    f.write("\n")
    for name, value in vars(v).items():
     if name in {'listener','buffer','pictures'}: continue
     f.write(f"{name}={repr(value)}\n")

 else:
  try:
   with open(f'saves/{p.save}.txt', 'r') as f:
    for line in f:
     if '=' not in line: continue 
     key, value = line.strip().split('=', 1)
     try: parsed = ast.literal_eval(value)
     except: continue
     if key == 'regions':
      w.regions = [region.from_dict(d) if d is not None else None for d in parsed]
     elif key == 'units':
      w.units = [unit.from_dict(d) if d is not None else None for d in parsed]
     elif key == 'auths':
      w.auths = [authority.from_dict(d) if d is not None else None for d in parsed]
     elif key == 'investment':
      p.investments = [investment.from_dict(d) for d in parsed]
     elif hasattr(w, key): setattr(w, key, parsed)
     elif hasattr(p, key): setattr(p, key, parsed)
  except: pass

#!gameplay
def investmentHelp(idx= 0, get= False):
 if not get:
  if not p.investments[idx].enabled: return
  if p.storage[p.investments[idx].resource]>= p.investments[i].amount:
   p.storage[p.investments[idx].resource]-= p.investments[i].amount
  else: return
  if p.investments[idx].time!=-1:
   p.investments[idx].current+= 1
  if p.investments[idx].current>= p.investments[idx].time and p.investments[idx].time!=-1:
   if p.investments[idx].type<= 15:
    p.advancements[p.investments[idx].type//4]= max(p.advancements[p.investments[idx].type//4], p.investments[idx].type% 4)
   elif p.investments[idx].type<= 19: pass
   elif p.investments[idx].type<= 23:
    w.regions[p.investments[idx].value].building= p.investments[idx].type% 4
    p.investments[idx].enabled= False
    return
   del p.investments[i]

 else:
  colNames= ["yellow", "red", "black", "white"]
  if p.investments[idx].type<= 15:
   return f"recieve {advNames[p.investments[idx].type//4] [p.investments[idx].type% 4]} from {colNames[p.investments[idx].type//4]}"
  elif p.investments[idx].type<= 19:
   return f"activate {polNames[p.investments[idx].type% 4]}"
  elif p.investments[idx].type<= 23:
   return f"build {buildNames[p.investments[idx].type% 4]}"
  elif p.investments[idx].type<= 27:
   return f"start {eventNames[p.investments[idx].type% 4]}"

def newUnit(val):
 w.units.append(unit([val, 2])) 
 p.unitNums.append(len(w.units)-1)
def newAuth(val):
 w.auths.append(authority([val, 2]))
 gameHelp(0, len(w.auths)-1)

def gameHelp(index=0, val=0): #0- auth claim 1- unit goto 2- checkAuth 3- attackAuth 4-checkGoal
 if index==0:
  authRegion = w.auths[val].loc[0]
  best = None
  bestDist = float('inf')
  for r in w.regions:
   if r.resource != -1 and not r.claimed:
    dist = abs(r.loc - authRegion)   
    if dist < bestDist:
     bestDist = dist
     best = r
  if best is not None:
   best.claimed = True
   w.auths[val].claims.append(w.regions.index(best))

 elif index== 1:
  if w.units[val] is None: return
  direct = w.units[val].goto - w.units[val].loc[0]
  if direct > w.mapSize / 2:
   direct -= w.mapSize
  elif direct < -w.mapSize / 2:
   direct += w.mapSize

  if direct > 0:
   w.units[val].loc[0]= (w.units[val].loc[0] + min(22, direct)) % w.mapSize
   w.units[val].flipped= False
  elif direct < 0:
   w.units[val].loc[0]= (w.units[val].loc[0] + max(-22, direct)) % w.mapSize
   w.units[val].flipped= True
  gameHelp(2, val)

 elif index== 2:
  if w.units[val].prepare!=-1 and val in p.unitNums:
   thr= w.auths[w.units[val].prepare].threats
   if not (val in thr):
    w.auths[w.units[val].prepare].threats.append(val)
   for i in range(len(thr)):
    if w.units[thr[i]].loc[0]// w.regionWidth!= w.auths[w.units[val].prepare].loc[0]// w.regionWidth: break
    if i== len(thr)-1:
     gameHelp(3,w.units[val].prepare)

 elif index==3:
  for i in range(len(w.auths[val].threats)-1, -1, -1):
   chance = w.units[w.auths[val].threats[i]].power/ (w.auths[val].level + w.units[w.auths[val].threats[i]].power)
   w.auths[val].health-= random.uniform(0.8, 1.0)* chance* 20
   if w.auths[val].health<= 0:
    for cla in w.auths[val].claims:
     w.regions[cla].claimed= False
    for uniIdx in w.auths[val].threats:
     w.units[uniIdx].prepare= -1
    w.auths[val]= None
    return
   if random.random() > chance:
    del p.unitNums[w.auths[val].threats[i]]
    w.units[w.auths[val].threats[i]]= None
    del w.auths[val].threats[i]
  if len(w.auths[val].threats)==0:
   w.auths[val].health= 100
 
 elif index==4:
  if p.goals[p.goalIdx]== 0:
   if w.auths[p.goalIdx] is None:
    p.goalPass= True
  elif p.goals[p.goalIdx]== 1:
   if len(p.unitNums)>= p.goalIdx*8:
    p.goalPass= True
  elif p.goals[p.goalIdx]== 2:
   if p.storage[3]>= 20* p.goalIdx:
    p.goalPass= True
  elif p.goals[p.goalIdx]== 3:
   if p.storage[5]>= 12* p.goalIdx:
    p.goalPass= True
  elif p.goals[p.goalIdx]== 4:
   if p.apoptosis> p.goalIdx* 15:
    p.goalPass= True
  elif p.goals[p.goalIdx]== 5: pass #mound
  elif p.goals[p.goalIdx]== 6: pass #migrate

def goalText(index= 0, level= 0): #0-destroyAuth 1-addUnits 2-addWood 3-addCopper 4-killUnit 5-makeMound 6-noMigrate
 if index== 0:
  return f"destroy authority {level}"
 elif index== 1:
  return f"have {level*8} units"
 elif index== 2:
  return f"have {level*20} wood"
 elif index== 3:
  return f"have {level* 12} copper"
 elif index== 4:
  return "apoptosis {level* 15} units"
 elif index== 5:
  return "build the mound"
 elif index== 6:
  return "do not migrate"

def begin():
 createMap()
 cursorVisible()
 saveLoad(True)

 img_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "img")
 try:
  for i, name in enumerate(pictureNames):
   path = os.path.join(img_dir, name)
   with open(path, 'r') as file:
    raw = file.read().strip()
   data = eval(f'[{raw}]', {"__builtins__": {}}, {})

   new_list = [[
    int(idx[0]) % 16,
    int(idx[0]) // 16,
    int(idx[1]) // (256 * 256),
    int(idx[1]) // 256 % 256,
    int(idx[1]) % 256,
    ]
    for idx in data[1:]
   ]
   if new_list:
    max_y = max(pi[1] for pi in new_list)
    for pi in new_list:
     pi[1] = max_y - pi[1]
   v.pictures.append(new_list)
  for i in range(4):
   if p.advancements[i] < 3:
    p.investments.append(investment(i * 4 + p.advancements[i]))
  for i in range(p.advancements[2]):
   p.investments.append(investment(20 + i))

 except Exception as e:
  print(f"Error loading images from '{img_dir}': {e}")
  v.running = 2

def gameLoop(looped= True):
 while True:
  if v.running!= 0: continue
  if len(v.buffer)==0: continue
  try:
   w.delay+=1
   if w.delay>=100000000: w.delay=0
   drawOn= True

   for i in range(len(p.investments)):
    investmentHelp(i)

   for i in range(len(w.units)):
    if w.units[i] is not None:
     if w.units[i].weak>0:
      w.units[i].weak-=1
     if w.units[i].broken>0:
      w.units[i].broken-=1

   if w.delay% 4== 0: 
    drawOn= True
    for i in range(len(p.storage)):
     outcome= p.storage[i]+ p.profits[i]
     if outcome<0:
      if i== 0: 
       if random.random()< -outcome/10:
        if len(p.unitNums)>0:
         w.units[p.unitNums[0]]= None
         del p.unitNums[0]

     p.storage[i]= max(0, outcome)

   if w.delay% 2== 0: 
    drawOn= True
    for i in range(len(w.units)):
     if w.units[i] is not None:
      gameHelp(1, i)

   if w.delay% 55== 0:
    gameHelp(4)
    if p.goalPass:
     p.goalIdx+= 1
     if not len(p.goals)>p.goalIdx:
      for i in range(10):
       p.goals.append(random.randint(0,6))
     if p.goals[p.goalIdx]== 0:
      allLocs = [i for i in range(len(w.regions)) if not w.regions[i].claimed]
      while (len(w.auths)-1)- p.goalIdx<= 0 and len(allLocs)>0:
       newInt= random.randint(0,len(allLocs)-1)
       newAuth(allLocs[newInt])
       del allLocs[newInt]
     if p.goals[p.goalIdx] in [6]: p.goalPass= True
     else: p.goalPass= False
    else:
     v.running= 1
     v.status= "game ended enter+ 'new'+ enter"
     p.lost= True
 
   if drawOn:
    for i in range(v.xy[1]): graphics(i)
   draw()
   if not looped: return
   threading.Event().wait(v.options[1]/ 100)
  except:
   v.running= 1
   termios.tcsetattr(fd, termios.TCSADRAIN, oldSettings)
   traceback.print_exc()
    
#!gameplayEnd

begin()
threading.Thread(target=inputLoop, daemon=True).start()
threading.Thread(target=gameLoop, daemon=True).start()
while v.running!=2:
 try:
  size = os.get_terminal_size()
  if v.xy!=[size.columns,size.lines]:
   if [size.columns, size.lines]==[0,0]: continue
   v.xy=[size.columns, size.lines]
   v.buffer=[[""]* v.xy[1], [""]* v.xy[1]]
   v.buffer[1][-1]= "enter+ 'h'+ enter"
   for y in range(v.xy[1]-1):
    graphics(y)
   draw()
  
  v.fpsTime = time.time()
  time.sleep(0.001)
 except Exception as e:
  v.running=1
  termios.tcsetattr(fd, termios.TCSADRAIN, oldSettings)
  traceback.print_exc()

termios.tcsetattr(fd, termios.TCSADRAIN, oldSettings)