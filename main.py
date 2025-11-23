import sys,os,random,time,termios, tty, math
import shutil, traceback
from opensimplex import OpenSimplex
from pynput import keyboard
from pynput.keyboard import Key, Listener

commands= ["help", "pause", "census", "focus", "diplomacy", "defensive", "expansive", "militaristic", "new"]
aliases= ["h", "p", "c", "f", "d", "def", "exp", "mil"]#ends at militaristic
allTexts=[
["controls:","wasd/qe/enter","1-notes 2-population", "3-influence 4-groups", "5-builds", "menu:", "new","commands:"]+ 
commands[:5]+ ["aliases:"]+ aliases+ ["!advance help!:","investment-","# [Y/n] to enable", "eg- '3 y'", "[citizens,influence,", "military,time]","build-","(maintained-_ mound-A farm-#)"],#state0
[],
["census:", "citizens-", "military-", "diseased-", "investments-"], #state2
["focuses:", "focus-", "investments-"],
["diplomacy:", "nations-", "investments-"],
["End:", "[citizens,military", "influence](peak)-", "(current)-", "formula:", "(ci/2+m)*i | peak/3+current"] #state5
]

codeInv=[[0.1,0.2,0.0,10], [0.2,0.1,0.1,15], [0.1,0.1,0.0,9], [0.1,0.0,0.2,4], [0.2,0.2,0.3,10], [0.3,0.1,0.1,20],[0.3,0.0,0.0,15],[0.1,0.1,0.1,6],[0.1,0.1,0.1,6]]   #0treaty envoy healer 3ceremony raid union 6mound migrateWest 8migrateEast
reset = "\033[0m"

class variables():
 buffer=[];
 xy=[70,20]
 seed=-1
 scale=3.65
 threshold=11;
 playerConsole= False
 mapScroll=[0,0]
 mapSize=[70,20]
 console=""
 windowState=0
 windowText=[""]
 cells=[]
 delay=0
 mapMode= 0 #0-greenBlue, 1-popDensity (light-dark), 2-influence(black-purple), 3-groups (rgb or black), 4-builds
 average=0
 windowScroll=0
 difficulty=5
 speed=1.3
 pId=0
 robots=[]
 areas=[]
 players=[]
 chunkSize=5
 notifications=[] #[location,char,timer=15]
 pause=False
 debugText=0
 timeLeft= [22,100]
 history=[[""]*10,0]
 totalInvs=1
 alwaysMaxed=0
v=variables()

class cell():
 def __init__( self,po=80, gro=[0.0,0.0,0.0]):
  self.outGroups= [0.0,0.0,0.0]
  self.building=0 #0-none 1-maintained 2-mound 3-farm
  self.population=po
  self.inGroups=gro

class player():
 def __init__(self,gro=0, ro=True):
  self.disease=[0,0] #0-none 1-mild 2-heavy
  self.focus=1 #0-defensive 1-expansive 2-military
  self.citizens=0
  self.military=0
  self.investments=[]
  self.influences=[]
  self.relations=[]
  self.availableLands=[]
  self.group=gro
  self.robot=ro
  self.claims=[[],[]] #0-rival 1-treaty
  self.peaks=[0,0,0] #0-pop 1-mil 2-inf

class investment():
 def __init__( self, na="", co=0, wi=0):
  self.id= v.totalInvs
  self.enabled=False
  self.value=0
  self.name=na
  allDemand=[]
  v.totalInvs+=1
  for i in range(3):
   idx=0.0
   if codeInv[co][i]!=0.0:
    idx= random.uniform(codeInv[co][i]-0.05, codeInv[co][i])
   allDemand.append(idx)
  allDemand.append(codeInv[co][3])
  self.demands= allDemand#0-pop 1-inf 2-mil 3-time
  self.window=wi
  self.code=co

def pickColor(r, g, b):
 return f"\033[48;2;{r};{g};{b}m"

def disableControls():
 old_settings = termios.tcgetattr(sys.stdin)
 iflag, oflag, cflag, lflag, ispeed, ospeed, cc = termios.tcgetattr(sys.stdin)
 
 iflag &= ~termios.IXON
 iflag &= ~termios.ISTRIP
 iflag &= ~termios.ICRNL
 iflag &= ~termios.INLCR
 iflag &= ~termios.IGNCR
 new_settings = [iflag, oflag, cflag, lflag, ispeed, ospeed, cc]
 termios.tcsetattr(sys.stdin, termios.TCSANOW, new_settings)
 return old_settings

def getArea(index,z,z2=-1):
 if z2==-1: z2=z
 allCells=[]
 for y in range(index//v.mapSize[0], index//v.mapSize[0]+z2):
  for x in range(index%v.mapSize[0], (index+z)%v.mapSize[0]):
   cellIdx= y* v.mapSize[0]+ x
   if v.cells[cellIdx]:
    allCells.append(cellIdx)
 return allCells

def convertCell(set=0, idx=0):
 if set==0: #cellToGrid
  chunkX = (idx % v.mapSize[0]) // v.chunkSize
  chunkY = (idx // v.mapSize[0]) // v.chunkSize
  areaIndex = chunkY * (v.mapSize[0] // v.chunkSize) + chunkX
  return areaIndex
 elif set==1 or set==2: #gridToCell/ all cells
  chunkX = idx % (v.mapSize[0] // v.chunkSize)
  chunkY = idx // (v.mapSize[0] // v.chunkSize)
  cellX = chunkX * v.chunkSize
  cellY = chunkY * v.chunkSize
  index= cellY * v.mapSize[0] + cellX
  if set==1: return index
  total=[]
  for cellIdx in getArea(index,v.chunkSize):
   total.append(cellIdx)
  return total

def updateVar(index=0,val=[]):
 if index==0:#investCreate [name,code,win]
  for inv in v.players[v.pId].investments:
   if val[1]== inv.code: return
  v.players[v.pId].investments. append(investment(val[0], val[1], val[2]))
  v.notifications.append([val[3], ['C','F','D'][val[2]], 12]) #pos char time=15

 elif index==1:#[playerId,infAmount,cellI]
  v.players[val[0]].influences. append([val[1],val[2]])
  areaIndex = convertCell(0,val[2])
  if not v.pId in v.areas[areaIndex] and len(v.areas[areaIndex])>0:
   v.notifications.append( [val[2],9,'D'])
   for i in range(len(v.areas[areaIndex])):
    relateNum= v.players[v.pId].relations [v.areas[areaIndex][i]]
    if relateNum==-1.0:
     v.players[v.pId].relations [v.areas[areaIndex][i]]=0.4
     updateVar(0, [f"n{v.areas[areaIndex][i]} treaty", 0, 2, convertCell(1, i)])
     v.players[v.pId].claims[0] .append(v.areas[areaIndex][i])
  v.areas[areaIndex].append(val[0])
  if val[1]>=0.5:
   for idx in checkCross(val[2]):
    v.players[val[0]]. availableLands.append(idx)

def printLine(y,text=""):
 print(f"\033[{y+1};1H", end="")
 print("\033[K", end="")
 print(text, end="")

def drawLine(y):
 if not v.buffer[y]: return
 v.buffer[y]=False
 line= ""
 if y<v.xy[1]-1:
  windowI=0
  for x in range(v.xy[0]):
   if not (y<int(v.xy[1]*0.5) and int(v.xy[0]*0.5)<x and v.windowState>-1):
    if (0 <= x + v.mapScroll[0] < v.mapSize[0] and 0 <= y + v.mapScroll[1] < v.mapSize[1]):
     index= v.mapSize[0] * (y + v.mapScroll[1]) + (x + v.mapScroll[0])
     if index < len(v.cells):
      if v.cells[index]:
       newChar=' '
       if v.mapMode==0:
        line+= pickColor(11, 111, 16)

       elif v.mapMode==1:
        green= min(255,int(88* (max(1,v.cells[index].population)/ max(v.average,1))/4))
        line+= pickColor(11, green, 16)

       elif v.mapMode==2:
        color=0    
        for i in range(len(v.players[v.pId].influences)): 
         if v.players[v.pId]. influences[i][1]== index:
          color= min(255,int(155* v.players[v.pId].influences[i][0])+6)
        line+= pickColor(color, 37, color)

       elif v.mapMode==3:
        inGro=v.cells[index].inGroups
        total = sum(inGro)
        r = int((inGro[0] / total) * 211)
        g = int((inGro[1] / total) * 211) 
        b = int((inGro[2] / total) * 211)
        line += pickColor(r, g, b)

       elif v.mapMode==4:
        newChar=[' ', '_', 'A', '#'] [v.cells[index].building]
        line+= pickColor(11, 111, 16)

       if v.mapMode==0:
        for i in range(len(v.notifications)):
         if index== v.notifications[i][0]:
          newChar= v.notifications[i][1]
       if not isinstance(newChar, str):
        newChar="H"
       line+=newChar
      else:
       line+= pickColor(11, 22, 111)
       line+=' '
   else:
    if len(v.windowText)>y:
     if windowI==0: line+=reset
     if len(v.windowText[y])>windowI:
      line+=v.windowText[y][windowI]
      windowI+=1
 else:
  if v.playerConsole:
   line+= v.console 
  else:
   pauseText=""
   if v.pause and (v.delay//80)%4!=0: pauseText="!P"
   pl= v.players[v.pId]
   dis=""
   if pl.disease[0]==2:
    dis="!!!"
   line+= f"{pauseText}c:{pl.citizens}/m:{pl.military}/f:{pl.focus}/t:{len(pl.influences)}/{dis}d:{pl.disease[0]}/e:{v.timeLeft[0]}"
 line+=reset
 printLine(y,line)
 print( f"\033[{v.xy[1]};{len(v.console)+1}H", end='', flush=True)
 sys.stdout.flush()

def createMap(see=-1):
 v.players= [player(2,False)]
 v.timeLeft[0]= v.timeLeft[1]
 v.cells, v.notifications= [],[]
 if see==-1:
  see= random.randint(0, 10000)
  v.seed= see
 noise = OpenSimplex(seed=see)
 noiseTwo= OpenSimplex(seed=see+1)
 v.areas= [[] for _ in range((v.mapSize[0]//5) * (v.mapSize[1]//5))]
 start, newRand=[0,0],[]
 v.buffer=[True]* len(v.buffer)

 for i in range(len(v.areas)//6):
  newRand.append(random.randint(0, len(v.areas)-1))

 for y in range(v.mapSize[1]):
  for x in range(v.mapSize[0]):
   n = noise.noise2(x*v.scale/v.mapSize[0], y*v.scale/v.mapSize[1])
   distance = 0
   if n > v.threshold/100:
    n2 = (max(0.05,noiseTwo.noise2( x*v.scale/v.mapSize[0]*1.8, y*v.scale/v.mapSize[1]*1.8))*110)
    dx = x - v.mapSize[0]/2
    dy = y - v.mapSize[1]/2
    distance = math.sqrt(dx*dx + dy*dy)
    angle_rad = math.atan2(dy, dx)
    groups = [
    (math.cos(angle_rad) + 1) / 2,
    (math.cos(angle_rad - 2*math.pi/3) + 1) / 2,
    (math.cos(angle_rad - 4*math.pi/3) + 1) / 2 ]
    v.cells.append(cell(int(n2),groups))
    groupValue=max(groups)
    groupI=groups.index(groupValue)
    if groupI==2:
     if start[0]<n2* groups[2]:
      start=[n2* groups[groupI], v.mapSize[0]* y+ x]
    newNum= convertCell(0,y* v.mapSize[0]+ x)
    if newNum in newRand:
     indexRand= newRand.index(newNum)
     v.areas[newNum].append(len(v.players))
     v.players.append(player(groupI))
     del newRand[indexRand]  

   else:
    v.cells.append(None)
 v.notifications.append([start[1],'H',15])

 for i in range(len(v.players)):
  relation=-1.0
  if i==v.pId:
   relation=1.0
  v.players[v.pId].relations. append(relation)
 updateVar(1, [v.pId,0.2,start[1]])  
 v.buffer=[True]*v.xy[1]

def checkCross(index):
 current_col = index % v.mapSize[0]
 current_row = index // v.mapSize[0]
 directions = [
        (current_col + 1, current_row),
        (current_col - 1, current_row),
        (current_col, current_row + 1),
        (current_col, current_row - 1)]
 added = []
 avoid = [idx[1] for idx in v.players[v.pId].influences]
 for col, row in directions:
  if 0 <= col < v.mapSize[0] and 0 <= row < v.mapSize[1]:
   cell_idx = row * v.mapSize[0] + col
   if cell_idx < len(v.cells) and v.cells[cell_idx] and cell_idx not in avoid:
    added.append(cell_idx)
 return added

def investmentDone(indexInv=-1):
 inv= v.players[v.pId].investments[indexInv]
 index= inv.code
 if index==0:
  idx= int(inv.name.split()[0][1:])
  if idx in v.players[v.pId].claims[0]:
   v.players[v.pId].claims[0].remove(idx)
   v.players[v.pId].claims[1].append(idx)
 if index==1 or index==0:
  idx= int(inv.name.split()[0][1:])
  v.players[v.pId].relations[idx]+= inv.value/(int(index==0)*3+1)/1000
 elif index==2:
  v.players[v.pId].disease[1]-= inv.value/300
 elif index==3:
  for i in range(len(v.players[v.pId].influences)):
   v.players[v.pId].influences[i][0]+= inv.value/2000
 elif index==4:
  idx= int(inv.name.split()[1][1:])
  if v.players[idx].robot:
   for i in range(len(v.areas)):
    if idx in v.areas[i]:
     areaCells=convertCell(2, i)
     for i in range(len(areaCells)):
      if i<int(len(areaCells)/min(2,inv.value/400)):
       break
      updateVar(1,[v.pId,0.3,areaCells[i]])
     break
  else:
   for i in range(len(v.players[idx].influences)-1, -1, -1):
    if i<int(len(v.players[idx].influences)/min(2,inv.value/400)): break
    updateVar(1, [v.pId,*v.players[idx].influences[i]]) 
    v.players[idx].influences.pop()

 elif index==5:
  idx= int(inv.name.split()[0][1:])
  if v.players[idx].robot:
   newInf= []
   val= min(1.0,inv.value/2200)
   for i in range(len(v.areas)):
    if idx in v.areas[i]:
     for cel in convertCell(2,i):
      newInf.append([val,cel])
   for inf in newInf:
    updateVar(1, [v.pId,*inf]) 
  else:
   newInf= v.players[idx].influences
   for inf in newInf:
    inf[0]= min(inf[0]* inv.value/2000,1.0)
   for inf in newInf:
    updateVar(1, [v.pId,*inf])
   v.players[idx].influences= []
 elif index==6:
  v.cells[v.players[v.pId]. influences[0][1]]. building=2
  for i in range(len(v.players[v.pId].influences)):
   if i==0: continue
   inf= v.players[v.pId].influences[i]
   totalPop= int(v.cells[inf[1]].population*inf[0]*0.7*inv.value/2000)
   v.cells[inf[1]].population-=totalPop
   v.cells[v.players[v.pId]. influences[0][1]].population+=totalPop
 elif index==7 or index==8:
  startArea=0
  if index==8: startArea=v.mapSize[0]/2-1
  allCells= getArea(startArea,v.mapSize[0]//2,v.mapSize[1]-1)
  if len(allCells)>0:
   randomI= random.choice(allCells)
   for i in range(len(v.areas)):
    if v.pId in v.areas[i]:
     v.areas[i].remove(v.pId)
    v.players[v.pId].claims=[[],[]]
   v.players[v.pId].influences=[]
   updateVar(1, [v.pId,1.0,randomI])
   v.cells[randomI].population+= int(inv.value//300)
   v.players[v.pId].disease=[0,0]

def gameLoop():
 if v.pause: return
 if v.delay%200==0:
  v.notifications.reverse()
  for i in range(len(v.notifications)-1, -1,-1):
   if isinstance(v.notifications[i][2], int):
    v.notifications[i][2]-=1
    if v.notifications[i][2]<=0:
     del v.notifications[i]

 if v.delay%max(1,int(96*v.speed))==0:
  v.timeLeft[0]-=1
  if v.timeLeft[0]==0:
   v.windowState=5
   consoleShow()
  if v.timeLeft[0]==-1:
   v.pause=True
  if v.timeLeft[0]== int(0.25*v.timeLeft[1]):
   v.players[v.pId].disease= [2,25]
   updateVar(0,["migrate east",8,1, v.players[v.pId].influences[0][1]])
   updateVar(0,["search healer",2,0, v.players[v.pId].influences[0][1]])
  if (v.timeLeft[0]+1)% int(0.4*v.timeLeft[1])== 0:
   updateVar(0,["construct mound",6,0, v.players[v.pId].influences[0][1]])

  inv=v.players[v.pId].investments
  if len(inv)>0:
   for i in range(len(inv)-1, -1, -1):
    if not inv[i].enabled:
     continue
    inv[i].demands[3]-=1
    for inf in v.players[v.pId].influences:
     first= inf[0]*v.cells[inf[1]].population *inv[i].demands[0]
     second= inf[0]*inv[i].demands[1]
     third= v.players[v.pId].military*inv[i].demands[2]
     inv[i].value+= second*100+first+third*2
     v.cells[inf[1]].population-=first
    if inv[i].demands[3]<=0:
     investmentDone(i)
     del inv[i]

 if v.delay%max(1,int(63*v.speed))==0:
  for i in range(len(v.cells)):
   if v.cells[i]:
    extra= max(1,int(v.cells[i].building==3)*1.2)
    growth = max(1, v.cells[i].population // 100* extra)
    v.cells[i].population = min(v.cells[i].population + growth, 9999999)

  for i in range(len(v.areas)):
   for j in range(len(v.areas[i])):
    if v.areas[i][j]>=len(v.players):
     if not v.players[v.areas[i][j]].robot:
      continue
     thisGroup= v.players[v.areas[i][j]].group
     allIndexes= convertCell(2, i)
     for idx in allIndexes:
      v.cells[idx].inGroups[thisGroup]+= 0.005

  for i in range(len(v.players)):
   if not v.players[i].robot: continue
   for inf in v.players[i]. influences:
    v.cells[inf[1]]. inGroups[v.players[v.pId].group]+= 0.01

  v.players[v.pId].disease[1]-=1
  if v.players[v.pId].disease[1]<=0:
   v.players[v.pId].disease[0]=0

  if random.random() < 0.05 and v.players[v.pId].disease[0]== 0:
   v.players[v.pId].disease= [1,20]
   updateVar(0,["migrate west",7,1,v.players[v.pId].influences[-1][1]])
   updateVar(0,["search healer",2,0, v.players[v.pId].influences[0][1]])

  if random.random() < 0.1:
   infCell= v.players[v.pId].influences[ random.randint(0, len(v.players[v.pId]. influences)-1)][1]
   if v.cells[infCell].building==0:
    v.cells[infCell].building= [1,3][random.randint(0,1)]
  if random.random() < 0.35:
   for plI in range(len(v.players)):
    if plI==v.pId: continue
    if plI in v.players[v.pId].claims[0]:
     v.players[v.pId].relations[plI]= max(0.0, v.players[v.pId].relations[plI]-0.04)
     if v.players[v.pId].relations[plI] <0.3:
      updateVar(0,[f"attack n{plI}",4,2, v.players[v.pId].influences[-1][1]])
    else:
     v.players[v.pId].relations[plI]= min(1.0, v.players[v.pId].relations[plI]+0.04)
     if v.players[v.pId].relations[plI]==1.0:
      for i in range(len(v.areas)):
       if plI in v.areas[i]:
        locUnion= convertCell(1,i)
      updateVar(0,[f"n{plI} union",5,2, locUnion])

  fightRand=random.random()
  if fightRand < 0.3:
   for relationI in range(len(v.players[v.pId].relations)):
    if v.players[v.pId].relations[relationI]< 0.3:
     if fightRand< 0.15 and v.players[v.pId].military>=  v.players[relationI].military:
      successLoc= v.players[v.pId].influences[0][1]
      for i in range(len(v.areas)):
       if relationI in v.areas[i]:
        successLoc= convertCell(1, i)
      updateVar(0,["ceremony",3,1, successLoc])
      if v.players[relationI].robot:
       v.players[v.pId]. influences[-1][0]= 1.0
      else:
       updateVar(1, [v.pId,*v.players[relationI]. influences[-1]])
       v.players[relationI]. influences.pop()
     v.players[v.pId].military= int(v.players[v.pId].military*0.85)
     v.players[relationI].military= int(v.players[relationI].military*0.85)

 if v.delay%max(1,int(80*v.speed))==0:
  allInf=0.0
  allCit=0
  allMaxed=True
  for i in range(len(v.players[v.pId].influences)):
   val1=max(i,1) if v.players[v.pId].focus==0 else max(i,1)*2
   val2=max(i,1) if v.players[v.pId].focus==2 else max(i,1)*2
   val3= max(i,1) if v.players[v.pId].focus==1 else max(i,1)*2
   oldInf= v.players[v.pId]. influences[i].copy()
   hasMain= max(int(v.cells[v.players[v.pId].influences[i][1]].building==1)*1.2,1)
   hasFarm= max(int(v.cells[v.players[v.pId].influences[i][1]].building==3)*1.2,1)
   
   totalPop=0
   if v.cells[oldInf[1]].building==2:
    for cellIdx in getArea(oldInf[1],v.chunkSize):
     newPop= v.cells[cellIdx].population/10
     totalPop+= newPop
     v.cells[cellIdx].population-=newPop
   v.cells[oldInf[1]].population+= totalPop

   for pl in v.players:
    if pl.robot:
     pl.military+= int(v.players[v.pId].military*0.06)
   totalMil= int(oldInf[0] * v.cells[ oldInf[1]]. population/ (val2*20))
   v.players[v.pId].military= min(9999999,v.players[v.pId].military+ totalMil)
   totalMil=int(totalMil*(val1/20))
   v.cells[oldInf[1]].population= max(0,min(9999999,v.cells[ oldInf[1]].population-totalMil)+ oldInf[0]/val1*v.cells[ oldInf[1]].population/22*hasFarm)
   v.cells[oldInf[1]].population= max(0,v.cells[oldInf[1]].population/(v.players[v.pId].disease[0]*0.2+1))
   v.cells[oldInf[1]].inGroups[ v.players[v.pId].group]+= (oldInf[0]// val1)//2
   if 1.0!= v.players[v.pId].influences[i][0]:
    allMaxed=False
    v.players[v.pId] .influences[i][0]= min(1.0,oldInf[0]+ 0.3/val3/ (1+len(v.players[v.pId].claims[0])*hasMain))
   allInf+= v.players[v.pId] .influences[i][0]
   allCit+= int(v.players[v.pId] .influences[i][0]*v.cells[v.players[v.pId] .influences[i][1]].population)

   if oldInf[0]<0.5:
    if v.players[v.pId] .influences[i][0]>=0.5:
     for idx in checkCross(v.players[v.pId] .influences[i][1]):
      v.alwaysMaxed=0
      v.players[v.pId]. availableLands.append(idx)

   if len(v.players[v.pId]. availableLands)>0:
    randomLand= random.choice( v.players[v.pId]. availableLands)
    updateVar(1, [v.pId,0.0,randomLand])
    v.players[v.pId]. availableLands.remove(randomLand)

  if allMaxed and v.alwaysMaxed<2:
   v.alwaysMaxed+=1
   updateVar(0,["migrate west",7,1,v.players[v.pId].influences[-1][1]])
   for inf in v.players[v.pId].influences:
    for idx in checkCross(inf[1]):
     v.players[v.pId]. availableLands.append(idx)


  alls=[allCit,v.players[v.pId].military, allInf]
  for i in range(3):
   if alls[i]> v.players[v.pId].peaks[i]:
    v.players[v.pId].peaks[i]=alls[i]
  v.players[v.pId].citizens= allCit
  v.buffer=[True]*v.xy[1]
  consoleShow()

def sortWindow(text=[]):
 if v.windowScroll+1>len(text):
  v.windowScroll= min(len(text)-1,v.windowScroll)
  return
 v.windowText= [""]* int(v.xy[1]*0.5)
 for i in range(v.windowScroll,len(text)):
  if len(v.windowText)>i- v.windowScroll and len(text)>i:
   v.windowText[(i- v.windowScroll)]+= f"{text[i]}"

def consoleShow():
 if v.windowState==-1 or v.windowState==1: return
 finalText,added= [],["",""]
 if v.windowState==2:
  added=["", v.players[v.pId].citizens,v.players[v.pId].military, ["none","mild","heavy"][v.players[v.pId].disease[0]]]

 elif v.windowState==3:
  focusStr = " ".join([f"!{word}!" if i == v.players[v.pId].focus else word for i, word in enumerate(commands[5:8])])
  added=["",focusStr]

 elif v.windowState==4:
  allRelations=[]
  for i in range(len(v.players[v.pId].relations)):
   relationAdded=f"n{i} "
   relationText="bad neutral good max"
   if i==v.pId:
    relationText=f"self {v.players[v.pId].relations[i]}"
   elif v.players[v.pId]. relations[i]>=1.0:
    relationText= relationText[:17]+ '>'+ relationText[17:] 
   elif v.players[v.pId]. relations[i]>=0.6:
    relationText= relationText[:12]+ '>'+ relationText[12:] 
   elif v.players[v.pId].relations[i]>=0.3:
    relationText= relationText[:4]+ '>'+ relationText[4:] 
   elif v.players[v.pId]. relations[i]>=0.0:
    relationText='>'+ relationText
   else:
    relationText="???"
   allRelations.append( relationAdded+relationText)
  added=["",allRelations]

 elif v.windowState==5:
  allInf= 0
  for idx in v.players[v.pId].influences:
   allInf+= idx[0]
  peakIdx= v.players[v.pId].peaks
  total= (peakIdx[0]/ 2+peakIdx[1]* peakIdx[2])/3+ (v.players[v.pId].citizens/ 2+v.players[v.pId].military* allInf)
  current=[v.players[v.pId].citizens, v.players[v.pId].military, allInf]
  added=["","", f"{peakIdx}",f"{current}","","", total]

 if v.windowState in [2,3,4]:
  pl= v.players[v.pId]
  allInvs=[]
  for inv in pl.investments:
   if inv.enabled: continue
   if inv.window!=v.windowState-2:
    continue
   allDems=""
   for i in range(3):
    if inv.demands[i]>0.2:
     allDems+="H,"
    elif inv.demands[i]>0.1:
     allDems+="M,"
    elif inv.demands[i]>0.0: 
     allDems+="L,"   
    else: 
     allDems+="0," 
   combindInv= f"{inv.id} {inv.name}:[{allDems}{inv.demands[3]}]"
   allInvs.append(combindInv)
  added.append(allInvs)

 for i in range(max(len(added),len( allTexts[v.windowState]))):
  if i<len(allTexts[v.windowState]):
   finalText.append( allTexts[v.windowState][i])
  if i<len(added):
   if added[i]!="": 
    if isinstance(added[i],list):
     for idx in added[i]:
      finalText.append(idx)
    else:
     finalText.append(added[i])
 sortWindow(finalText) 

def commandFuncs():
 newCom= commands[:5]+ aliases[:5]
 if v.console in newCom:
  v.windowState= newCom.index(v.console)% 5
 if v.console in [commands[1],aliases[1]]:
  v.pause= not v.pause
 elif v.console==commands[8]:
  createMap()
 elif v.console in commands[5:8]+ aliases[5:8]:
  v.players[v.pId].focus= (commands[5:8]+ aliases[5:8]).index(v.console)%3
 elif v.console!="":
  inv= v.players[v.pId]. investments
  words= v.console.split()
  if words[0].isdigit():
   for i in range(len(inv)):
    if inv[i].id==int(words[0]):
     if len(words)>1:
      if words[1]=='y':
       inv[i].enabled= True
     else:
      inv[i].enabled= True

 consoleShow()
 v.console=""
 v.playerConsole=False

def onPress(key):
 try:
  if key== Key.enter:
   v.buffer = [True]* v.xy[1]
   v.pause=False
   if v.playerConsole:
    if v.console!="":
     v.history[0].insert(0,v.console)
     v.history[0].pop()
     v.history[1]=-1
    commandFuncs()
   else:
    if v.windowState>-1:
     v.windowState=-1
    else: v.playerConsole=True
   cursorVisible()

  if key == Key.up or key== Key.down:
   v.playerConsole=True
   if key== Key.down: 
    v.history[1]=max(0,v.history[1]-1)
   else:
    v.history[1]= min(len(v.history[0])-1,v.history[1]+1)
   v.console= v.history[0][v.history[1]]
  if v.playerConsole:
   if key == Key.backspace:
    v.console=v.console[:-1]
   elif hasattr(key, 'char'):
    v.console += key.char.lower()
   elif key== keyboard.Key.space:
    v.console+= ' '
  else:
   if hasattr(key, 'char'):
    if key.char.lower() == 'a':
     v.mapScroll[0]= max(v.mapScroll[0]-v.xy[0]/10,0)
    elif key.char.lower() == 'd':
     v.mapScroll[0]= max(0,min(v.mapScroll[0]+v.xy[0]/10, v.mapSize[0]-v.xy[0]))
    elif key.char.lower() == 'w':
     v.mapScroll[1]= max(v.mapScroll[1]-v.xy[1]/10,0)
    elif key.char.lower() == 's':
     v.mapScroll[1]= max(0,min(v.mapScroll[1]+v.xy[1]/10, v.mapSize[1]-v.xy[1]+1))
    else:
     modes=['1','2','3','4','5']
     if key.char.lower() in modes:
      modeSet( modes.index(key.char.lower()))
     scroll= ['e','q']
     if key.char.lower() in scroll:
      v.windowScroll= max(0,v.windowScroll+ 1 - scroll.index(key.char.lower())*2)
      consoleShow()
      
    v.mapScroll=[int(i) for i in v.mapScroll]
    v.buffer=[True]* len(v.buffer)

 except Exception as e:
  traceback.print_exc()

def cursorVisible():
 if not v.playerConsole:#hide
  print('\033[?25l', end='', flush=True)
 else:
  print('\033[?25h', end='', flush=True)

def modeSet(mode=-1):
 if mode!=-1: v.mapMode= mode
 validCells = [cel for cel in v.cells if cel is not None]
 if v.mapMode==1:
  v.average= int(sum(cel.population for cel in validCells)/len(validCells))

createMap(v.seed)
cursorVisible()
disableControls()
oldSettings = termios.tcgetattr(sys.stdin)
tty.setcbreak(sys.stdin.fileno())

with Listener(on_press=onPress) as listener:
 try:
  while True:
   size = shutil.get_terminal_size()
   if v.xy!=[size.columns,size.lines]:
    if [size.columns, size.lines]!=[0,0]:
     v.xy=[size.columns, size.lines]
     v.buffer=[True]* v.xy[1] 
     v.windowText=[""]* int(v.xy[1]*0.5)
     consoleShow()

   v.buffer[v.xy[1]-1]=True
   for y in range(v.xy[1]):
    drawLine(y)
   v.delay+=1
   if v.delay> 1000000: v.delay=0
   gameLoop()
   print( f"\033]0;nationOnDust\007", end='', flush=True)
   #print( f"\033]0;{int(v.scale*1000)}/{v.delay}/{v.windowScroll}/{v.debugText}\007", end='', flush=True)
   time.sleep(0.01)
 finally:
  termios.tcsetattr(sys.stdin, termios.TCSADRAIN, oldSettings)