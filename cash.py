from __future__ import with_statement
import time, bisect, os, key_codes, collections, gc, weakref, zlib
import appuifw, graphics, e32, topwindow
import cPickle as pickle

__version__='2.1.0 beta'

ETimeFormat='%a %b %d %H:%M:%S %Y'

EDeal=[[-1, 1, 1, -1, 1], [1, -1, -1, 1, -1]]
EFrom, ETo=0, 1
EFromTo=[u'From', u'To']

EAssets, ELiabilities, EIncome, EExpenses, EEquity=0, 1, 2, 3, 4
ESeason=[None, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4]
ESettleNone, ESettleByMonth, ESettleBySeason=0, 1, 2

# Translation module
# TODO: need to be implemented as a class.
class Translator(object):
  def __init__(self, filename=None):
    self.translations = {}
    if filename: self.load(filename)
  def load(self, filename):
    self.clear()
    with open(filename) as f:
      for ln in f.readlines():
        ln=ln.strip()
        if not ln or ln.startswith('#'): continue
        try:
          x = eval('{\n%s\n}' % ln)
        except: raise ValueError('%s: syntax error' % repr(ln))
        if x:
          dst=x.values()[0].decode('utf-8')
          self.translations[x.keys()[0]]=dst
  def clear(self):
    self.translations={}
  def __getitem__(self, name):
    return self.translations.get(string, string)
  def __call__(self, string):
    return self.translations.get(string, string)
  def Time(self, t):
    return unicode(time.strftime(ETimeFormat, t))
  def updateConstants(self):
    global EItemType, EAccountType, ESettle
    EItemType=[T(u'From'), T(u'To')]
    EAccountType=[T(u'Assets'), T(u'Liabilities'),
      T(u'Income'), T(u'Expenses'), T(u'Equity')]
    ESettle=[T(u'None'), T(u'By the month'), T(u'By the season')]
    global EBool, EOrdinal, EMonth, EChange
    EBool=[T(u'Yes'), T(u'No')]
    EOrdinal=[None, T(u'first'), T(u'second'), T(u'third'),
      T(u'fourth')]
    EMonth=[None, T(u'Jan'), T(u'Feb'), T(u'Mar'), T(u'Apr'),
      T(u'May'), T(u'Jun'), T(u'Jul'), T(u'Aug'), T(u'Sep'),
      T(u'Oct'), T(u'Nov'), T(u'Dec')]
    EChange=[T(u'Save'), T(u'Discard')]
    global EBanner
    EBanner=[T(u'Cash - Financial Accounting Software'),
      u'-',
      T(u'Version: %s')%(__version__),
      u'Python for S60: %s'%e32.pys60_version,
      u'',
      u'Copyright (c) Sun 2013-2015']

# TODO
T=Translator('E:\\Python\\Cash\\Languages\\zh-CN.txt')
T.updateConstants()

# UndoRedo module
class MergeFunc(object):
  def __init__(self, funclist):
    self.funclist=funclist
  def __call__(self):
    funclist=[]
    for func in self.funclist:
      funclist.append(func())
    funclist.reverse()
    return MergeFunc(funclist)

def DoNothing():
  return DoNothing

class UndoRedo(object):
  # __modified:
  #   0 suggests 'not modified'
  #   positive suggests the number of steps to undo to origin
  #   negative suggests the number of steps to redo to origin
  #   None suggests it can never return to origin
  def __init__(self):
    self.undolist=[]
    self.redolist=[]
    self.modified=0
  def clear(self):
    self.undolist=[]
    self.redolist=[]
    if self.modified!=0: self.modified=None
  def resetModified(self):
    self.modified=0
  def isModified(self):
    return False if self.modified==0 else True
  def hasUndo(self):
    return len(self.undolist)
  def hasRedo(self):
    return len(self.redolist)
  def append(self, func, desc=u'', detail=u''):
    # TODO: implement detail
    self.undolist.append((func, desc))
    self.redolist=[]
    if not self.modified is None:
      if self.modified<0: self.modified=None
      else: self.modified+=1
  def undo(self):
    func, desc=self.undolist.pop()
    self.redolist.append((func(), desc))
    if not self.modified is None: self.modified-=1
  def redo(self):
    func, desc=self.redolist.pop()
    self.undolist.append((func(), desc))
    if not self.modified is None: self.modified+=1
  def go(self, index):
    if index>0:
      while index!=0:
        self.undo()
        index-=1
    elif index<0:
      while index!=0:
        self.redo()
        index+=1
  def goToOrigin(self):
    self.go(self.modified)

# Core module
class Item(object):
  # This class is a compatible layer between Deal and Account
  # THUS, DO NOT USE IT DIRECTLY
  def __init__(self, deal, type, account):
    # use "ref" rather than "proxy", due to e.g. "is" operator
    self.__deal=weakref.ref(deal) # readonly
    self.__type=type # readonly
    self.__account=weakref.ref(account)
  def __cmp__(self, other):
    if self is other: return 0
    if self.deal is other.deal:
      # e.g. when exchange "from" and "to" accounts
      return -1 if self.type==EFrom else 1
    return self.deal.__cmp__(other.deal)
  def __setAccount(self, account):
    if self.__account() is account: return
    if self.deal.established:
      self.__account().delItem(self)
    self.__account=weakref.ref(account)
    if self.deal.established:
      account.addItem(self)
  def listdesc(self): # UI related.
    return (self.deal.desc, T(u'%(sum)5.2f\xa5  %(time)s')%
      {'sum': self.sum,
       'time': T.Time(time.localtime(self.deal.time))})
  deal=property(lambda self:self.__deal())
  type=property(lambda self:self.__type)
  account=property(lambda self:self.__account(), __setAccount)
  sum=property(lambda self:EDeal[self.type][self.account.type]*
    self.deal.amount)

class Deal(object):
  @staticmethod
  def validData(data):
    # data: amount desc from to time
    return data[0]>0.0 and data[2] and data[3] and \
      data[2].established and data[3].established
  def __init__(self, deallist, amount=0.0, desc=u'',
      fr=None, to=None, t=None):
    # "from" is a keyword, so use "fr"
    self.__deallist=weakref.ref(deallist) # readonly
    self.__established=0
    self.desc=desc
    if amount>=0.0:
      self.__amount=amount
      self.items=(Item(self, EFrom, fr), Item(self, ETo, to))
    else:
      self.__amount=-amount
      self.items=(Item(self, EFrom, to), Item(self, ETo, fr))
    self.time=t if t else time.time()
  def __cmp__(self, other):
    assert self.deallist is other.deallist
    res=other.time-self.time
    if res>0: return 1
    elif res<0: return -1
    else:
      assert False
      return 0
  def __setEstablished(self, established):
    if self.__established==established: return
    assert self.valid()
    if established:
      self.__established=1
      self.deallist.addDeal(self)
      self.fr.addItem(self.items[EFrom])
      self.to.addItem(self.items[ETo])
    else:
      self.fr.delItem(self.items[EFrom])
      self.to.delItem(self.items[ETo])
      self.deallist.delDeal(self)
      self.__established=0
  def __setAmount(self, amount):
    if self.__amount==amount: return
    if self.established:
      oldfrom=self.items[EFrom].sum
      oldto=self.items[ETo].sum
    self.__amount=amount
    if self.established:
      deltafrom=self.items[EFrom].sum-oldfrom
      deltato=self.items[ETo].sum-oldto
      if deltafrom: self.fr.deltaSum(deltafrom)
      if deltato: self.to.deltaSum(deltato)
  def __setFr(self, fr):
    self.items[EFrom].account=fr
  def __setTo(self, to):
    self.items[ETo].account=to
  def valid(self):
    return Deal.validData(self.get())
  def get(self):
    return (self.amount, self.desc, self.fr, self.to, self.time)
  def set(self, data): # undoable
    # data: amount desc from to time
    # Notion: use "set" if you want to implement
    #   undo and redo function; otherwise, assign directly.
    old=self.get()
    self.amount, self.desc, self.fr, self.to, self.time=data
    return lambda: self.set(old)
  def establish(self, state): # undoable
    self.established=state
    return lambda: self.establish(1-state)
  def exchangeFromTo(self): # DEPRECATED; undoable
    self.fr, self.to=self.to, self.fr
    return lambda: self.exchangeFromTo()
  def tabdesc(self): # UI related.
    tab=self.desc
    if not self.valid(): tab+=T(u' (invalid)')
    return tab
  deallist=property(lambda self:self.__deallist())
  established=property(lambda self: self.__established,
    __setEstablished)
  amount=property(lambda self: self.__amount, __setAmount)
  fr=property(lambda self: self.items[EFrom].account, __setFr)
  to=property(lambda self: self.items[ETo].account, __setTo)

class DealList(object):
  def __init__(self, rootaccount):
    self.__rootaccount=weakref.ref(rootaccount)
    self.deallist=[]
  def load(self, deals):
    for deal in deals:
      Deal(self, deal[0], deal[1],
        self.rootaccount.getAccountByPath(deal[2]),
        self.rootaccount.getAccountByPath(deal[3]),
        deal[4]).established=1
    return True
  def save(self):
    deals=[(deal.amount, deal.desc, deal.fr.path,
      deal.to.path, deal.time) for deal in self.deallist]
    return deals
  def addDeal(self, deal):
    bisect.insort_left(self.deallist, deal)
  def delDeal(self, deal):
    self.deallist.remove(deal)
  rootaccount=property(lambda self:self.__rootaccount())

class Account(object):
  @staticmethod
  def validData(data):
    # data: name desc type placeholder parent pos
    return data[0] and data[2]>=0 and \
      data[4].established and data[4].placeholder
  def __init__(self, rootaccount, name=u'', desc=u'',
      type=-1, placeholder=0, parent=None, pos=None):
    self.__rootaccount=weakref.ref(rootaccount) #readonly
    self.__established=1 if self.isRoot() else 0
    self.name=name
    self.desc=desc
    self.__type=-1 if self.isRoot() else type if parent.isRoot() \
      else parent.type
    self.__placeholder=1 if self.isRoot() else placeholder
    self.__parent=None if self.isRoot() else weakref.ref(parent)
    self.__pos=pos
    self.sum=0.0 # update automatically
    self.items=[]
  def __setEstablished(self, established):
    if self.__established==established: return
    assert self.valid() and len(self.items)==0
    if established:
      self.__established=1
      self.parent.addItem(self, self.pos)
    else:
      self.parent.delItem(self)
      self.__established=0
  def __setType(self, type):
    if self.__type==type: return
    assert self.parent.isRoot() or self.parent.type==type
    self.__type=type
    if self.placeholder:
      for i in self.items:
        i.type=type
    # TODO: Can be optimized
    self.sum=sum([i.sum for i in self.items])
  def __setPlaceholder(self, placeholder):
    if self.__placeholder==placeholder: return
    assert len(self.items)==0
    self.__placeholder=placeholder
  def __setParent(self, parent):
    if self.__parent() is parent: return
    assert parent
    if self.established:
      self.__parent().delItem(self)
    self.__parent=weakref.ref(parent) if parent else None
    if not parent.isRoot():
      self.type=parent.type
    if self.established:
      parent.addItem(self, self.pos)
  def __setPos(self, pos):
    if pos==self.__pos: return
    assert self.established and \
      pos>=0 and pos<len(self.parent.items)
    if pos<self.__pos:
      for i in self.parent.items[pos:self.__pos]:
        i.__pos+=1
    else:
      for i in self.parent.items[self.__pos+1:pos+1]:
        i.__pos-=1
    # TODO: Can be optimized with "deque"
    self.parent.items.remove(self)
    self.parent.items.insert(pos, self)
    self.__pos=pos
  def __getParent(self):
    if self.__parent is None: return None
    else: return self.__parent()
  def __getPath(self):
    if self.isRoot(): return []
    else: return self.parent.path+[self.pos]
  def valid(self):
    return Account.validData(self.get())
  def get(self):
    return (self.name, self.desc, self.type, self.placeholder,
      self.parent, self.pos)
  def set(self, data): # undoable
    # data: name desc type placeholder parent pos
    old=self.get()
    assert data[4] or self.isRoot()
    if self.parent is data[4]:
      self.name, self.desc, self.type, self.placeholder=data[:4]
      self.pos=data[5]
    else:
      self.__pos=data[5]
      self.parent=data[4]
      self.name, self.desc, self.type, self.placeholder=data[:4]
    return lambda: self.set(old)
  def establish(self, state): # undoable
    self.established=state
    return lambda: self.establish(1-state)
  def moveTo(self, pos): # undoable
    oldpos=self.pos
    self.pos=pos
    return lambda: self.moveTo(oldpos)
  def moveUp(self): # undoable
    assert self.pos>0
    return self.moveTo(self.pos-1)
  def moveDown(self): # undoable
    assert self.pos<len(self.parents.items)-1
    return self.moveTo(self.pos+1)
  def clear(self): # undoable
    funclist=[]
    if self.placeholder:
      for account in self.items:
        funclist.append(account.clear())
      while len(self.items):
        funclist.append(self.items[0].establish(0))
    else:
      while len(self.items):
        funclist.append(self.items[0].deal.establish(0))
    funclist.reverse()
    return MergeFunc(funclist)
  def copy(self, rootaccount, parent):
    account=Account(rootaccount, self.name, self.desc, self.type,
      self.placeholder, parent, self.pos)
    account.established=1
    if self.placeholder:
      for i in self.items:
        i.copy(rootaccount, account)
  def isRoot(self):
    return False
  def isParent(self, account):
    # Notion: if "account" is "self", it will also return True.
    #   And it doesn't check whether it has been established
    while account:
      if account is self: return True
      account=account.parent
    return False
  def getAccountByPath(self, path):
    if len(path):
      if not self.placeholder:
        raise Exception('can\'t found the account')
      return self.items[path[0]].getAccountByPath(path[1:])
    else: return self
  def getAccountByName(self, path):
    if len(path):
      if not self.placeholder:
        raise Exception('can\'t found the account')
      for i in self.items:
        if i.name==path[0]:
          return i.getAccountByName(path[1:])
      raise Exception('can\'t found the account')
    else: return self
  def getFullname(self):
    name=self.name
    p=self.parent
    while not p.isRoot():
      name=p.name+u':'+name
      p=p.parent
    return name
  def updateSum(self):
    # Force to update "sum".
    # Usually not used, since "sum" updates automatically.
    self.sum=0.0
    if self.placeholder:
      for i in self.items:
        i.updateSum()
    for i in self.items:
      self.sum+=i.sum
  def deltaSum(self, delta):
    assert not self.isRoot()
    self.sum+=delta
    # avoid "-0.00" due to floating point errors
    self.sum=round(self.sum, 2)
    if self.established:
      if self.parent.isRoot():
        self.parent.deltaSumRoot(delta, self.type)
      else:
        self.parent.deltaSum(delta)
  def addItem(self, item, pos=None):
    if self.placeholder:
      assert self.isRoot() or self.type==item.type
      if pos is None:
        self.items.append(item)
        item.__pos=len(self.items)-1
      else:
        for i in self.items[pos:]:
          i.__pos+=1
        self.items.insert(pos, item)
    else:
      bisect.insort_left(self.items, item)
    if self.isRoot():
      self.deltaSumRoot(item.sum, item.type)
    else:
      self.deltaSum(item.sum)
  def delItem(self, item):
    pos=self.items.index(item)
    self.items.remove(item)
    if self.placeholder:
      for i in self.items[pos:]:
        i.pos-=1
    if self.isRoot():
      self.deltaSumRoot(-item.sum, item.type)
    else:
      self.deltaSum(-item.sum)
  def tabdesc(self): # UI related.
    tab=self.name
    if self.placeholder:
      tab+=u' +'
    if not self.valid():
      tab+=T(u' (invalid)')
    return tab
  def listdesc(self): # UI related.
    major=self.name
    if self.placeholder:
      major+=u' +'
    typesum=self.rootaccount.typesum[self.type]
    if typesum!=0.0 and self.sum!=0.0 and self.sum!=typesum:
      minor=u'%5.2f\xa5 (%.0f%%)  '%(self.sum,
        self.sum*100/typesum)
    else: minor=u'%5.2f\xa5  '%(self.sum)
    minor+=self.desc
    return (major, minor)
  rootaccount=property(lambda self:self.__rootaccount())
  established=property(lambda self: self.__established,
    __setEstablished)
  type=property(lambda self: self.__type, __setType)
  placeholder=property(lambda self: self.__placeholder,
    __setPlaceholder)
  parent=property(__getParent, __setParent)
  pos=property(lambda self: self.__pos, __setPos)
  path=property(__getPath)

class RootAccount(Account):
  def __init__(self, name=u''):
    Account.__init__(self, rootaccount=self,
      name=name if name else T(u'Root'))
    self.sum=0.0
    self.typesum=[0.0]*5
  def valid(self):
    return True
  def clear(self): # undoable
    funclist=[]
    while len(self.items):
      funclist.append(self.items[0].clear())
      funclist.append(self.items[0].establish(0))
    funclist.reverse()
    self.sum=0.0
    self.typesum=[0.0]*5
    return MergeFunc(funclist)
  def copy(self):
    account=RootAccount(self.name)
    for i in self.items:
      i.copy(account, account)
    return account
  def isRoot(self):
    return True
  def getFullname(self):
    return self.name
  def deltaSumRoot(self, delta, type):
    self.typesum[type]+=delta
    if type==EAssets:
      self.sum+=delta
    elif type==ELiabilities:
      self.sum-=delta
    self.typesum[type]=round(self.typesum[type], 2)
    self.sum=round(self.sum, 2)
  def load(self, accounts):
    for account in accounts:
      Account(self, account[1], account[2], account[3], account[4],
        self.getAccountByPath(account[0])).established=1
    return True
  def save(self):
    bfs=collections.deque(self.items)
    accounts=[]
    while len(bfs):
      account=bfs.popleft()
      accounts.append((account.parent.path, account.name,
        account.desc, account.type, account.placeholder))
      if account.placeholder:
        bfs.extend(account.items) 
    return accounts

class NameRule(object):
  @staticmethod
  def getDict(book):
    return {'time': time.localtime(book.time), 'settle': book.settle,
      'period': book.period}
  @staticmethod
  def test(rule, book):
    # return a tuple with two elements "(first, second)"
    #   first: True->No error  False->Error occurred
    #   second: if no error, the result (type may vary)
    #     else the error message (unicode)
    if not rule: return (True, u'')
    try:
      name=eval(rule, NameRule.getDict(book))
    except Exception ,e:
      return (False, unicode(e))
    if not (type(name) is unicode):
      return (False, u'need unicode, '+
        unicode(type(name).__name__)+u' found')
    return (True, name)
  def __init__(self, settlerules, desc=u'', rule=u''):
    self.settlerules=weakref.proxy(settlerules)
    self.desc=desc
    self.rule=rule
  def run(self, book):
    # Return the error message(unicode) if error occurred
    result=NameRule.test(self.rule, book)
    if result[0]: book.name=result[1]
    else: return u'Name Rule: '+result[1]
  def get(self):
    return (self.desc, self.rule)
  def set(self, rule):
    old=self.get()
    self.desc, self.rule=rule
    return lambda: self.set(old)

class DescRule(object):
  @staticmethod
  def getDict(book):
    return {'name': book.name, 'time': time.localtime(book.time),
      'settle': book.settle, 'period': book.period}
  @staticmethod
  def test(rule, book):
    if not rule: return (True, u'')
    try:
      desc=eval(rule, DescRule.getDict(book))
    except Exception ,e:
      return (False, unicode(e))
    if not (type(desc) is unicode):
      return (False, u'need unicode, '+
        unicode(type(desc).__name__)+u' found')
    return (True, desc)
  def __init__(self, settlerules, desc=u'', rule=u''):
    self.settlerules=weakref.proxy(settlerules)
    self.desc=desc
    self.rule=rule
  def run(self, book):
    result=DescRule.test(self.rule, book)
    if result[0]: book.desc=result[1]
    else: return u'Descripition Rule: '+result[1]
  def get(self):
    return (self.desc, self.rule)
  def set(self, rule):
    old=self.get()
    self.desc, self.rule=rule
    return lambda: self.set(old)

class DealRule(object):
  @staticmethod
  def validData(self, data):
    return data[1] and data[2] and data[3] and data[4]
  @staticmethod
  def getDict(book, oldbook, type=0):
    values={'name': book.name,
      'time': time.localtime(book.time),
      'settle': book.settle, 'period': book.period}
    if type: values['accounts']=book.rootaccount
    else: values['accounts']=oldbook.rootaccount
    return values
  @staticmethod
  def test(amountrule, descrule, frrule, torule, book, oldbook):
    values1=DealRule.getDict(book, oldbook, 0)
    values2=DealRule.getDict(book, oldbook, 1)
    try:
      amount=eval(amountrule, values1)
      desc=eval(descrule, values1)
      fr=eval(frrule, values2)
      to=eval(torule, values2)
    except Exception ,e:
      return (False, unicode(e))
    if not (type(amount) is float):
      return (False, u'amount: need float, '+
        unicode(type(amount).__name__)+u' found')
    if not (type(desc) is unicode):
      return (False, u'desc: need unicode, '+
        unicode(type(desc).__name__)+u' found')
    if not (issubclass(type(fr), Account)):
      return (False, u'from: need account, '+
        unicode(type(fr).__name__)+u' found')
    if not (issubclass(type(to), Account)):
      return (False, u'to: need account, '+
        unicode(type(to).__name__)+u' found')
    if fr.placeholder:
      return (False, u'from: can\'t be placeholder')
    if to.placeholder:
      return (False, u'to: can\'t be placeholder')
    if amount<0:
      temp=fr
      fr=to
      to=temp
      amount=-amount
    return (True, (amount, desc, fr, to))
  def __init__(self, settlerules, desc=u'', amountrule=u'',
      descrule=u'', frrule=u'', torule=u''):
    self.settlerules=weakref.proxy(settlerules)
    self.desc=desc
    self.amountrule=amountrule
    self.descrule=descrule
    self.frrule=frrule
    self.torule=torule
  def run(self, book, oldbook):
    result=DealRule.test(*(self.get()[1:]+(book, oldbook)))
    if result[0]:
      deal=Deal(book.deallist, *result[1])
      if deal.amount==0.0: return
      if deal.valid():
        deal.established=1
        return
      error=u'deal is invalid'
    else: error=result[1]
    return u'Deal Rule '+unicode(
      self.settlerules.dealrules.index(self)+1)+u': '+error
  def get(self):
    return (self.desc, self.amountrule, self.descrule,
      self.frrule, self.torule)
  def set(self, rules):
    old=self.get()
    self.desc, self.amountrule, self.descrule, \
      self.frrule, self.torule=rules
    return lambda: self.set(old)

class SettleRules(object):
  def __init__(self):
    self.namerule=NameRule(self)
    self.descrule=DescRule(self)
    self.dealrules=[]
  def run(self, book, oldbook):
    errors=[]
    errors.append(self.namerule.run(book))
    errors.append(self.descrule.run(book))
    for i in self.dealrules:
      errors.append(i.run(book, oldbook))
    if any(errors): return u'\n'.join([i for i in errors if i])
  def copy(self):
    rules=SettleRules()
    rules.namerule.set(self.namerule.get())
    rules.descrule.set(self.descrule.get())
    for i in self.dealrules:
      rules.dealrules.append(DealRule(rules, *i.get()))
    return rules
  def set(self, data):
    olddata=self.get()
    namerule, descrule, dealrules=data
    self.namerule=NameRule(self, *namerule)
    self.descrule=DescRule(self, *descrule)
    for i in dealrules:
      self.dealrules.append(DealRule(self, *i))
    return lambda: self.set(olddata)
  def get(self):
    dealrules=[]
    for i in self.dealrules:
      dealrules.append(i.get())
    return (self.namerule.get(), self.descrule.get(), dealrules)
  def load(self, data):
    self.set(data)
    return True
  def save(self):
    return self.get()

class Book(object):
  @staticmethod
  def validData(data):
    # data: name desc time settle period settled
    return bool(data[0])
  @staticmethod
  def parsePeriod(settle, t=None):
    if t is None: t=time.time()
    t=time.localtime(t)
    if settle==ESettleNone: return None
    elif settle==ESettleByMonth: return (t[0], t[1])
    else: return (t[0], ESeason[t[1]])
  @staticmethod
  def nextPeriod(settle, period):
    assert settle!=ESettleNone
    if settle==ESettleByMonth:
      if period[1]==12: return (period[0]+1, 1)
      else: return (period[0], period[1]+1)
    else:
      if period[1]==4: return (period[0]+1, 1)
      else: return (period[0], period[1]+1)
  @staticmethod
  def isToBeSettled(settle, period):
    if settle==ESettleNone: return False
    if period<Book.parsePeriod(settle): return True
    else: return False
  def __init__(self, name=u'', desc=u'', t=None,
      settle=ESettleNone, period=None, settled=0):
    self.rootaccount=RootAccount()
    self.deallist=DealList(self.rootaccount)
    self.settlerules=SettleRules()
    self.name=name
    self.desc=desc
    self.time=t if t else time.time()
    self.__settle=settle
    self.__period=period if settle!=ESettleNone and \
      period else Book.parsePeriod(settle, self.time)
    self.settled=settled
  def __setSettle(self, settle):
    if self.__settle==settle: return
    self.__settle=settle
    self.period=None
    self.settled=0
  def __setPeriod(self, period): # None for default
    if period!=None and self.__period==period: return
    self.__period=period if self.settle!=ESettleNone and \
      period else Book.parsePeriod(self.settle, self.time)
  def valid(self):
    return Book.validData(self.get())
  def get(self):
    return (self.name, self.desc, self.time,
      self.settle, self.period, self.settled)
  def set(self, data): # undoable
    # data: name desc time settle period settled
    old=self.get()
    self.name, self.desc, self.time, self.settle=data[:4]
    self.period, self.settled=data[4:]
    return lambda: self.set(old)
  def doSettle(self):
    # return a tuple with two or three elements
    #   first: True->No error  False->Error occurred
    #   second: if no error, the book (book)
    #     else the error message (unicode)
    #   third: only exist when no error, the undo function
    assert self.settle!=ESettleNone
    book=Book(settle=self.settle,
      period=Book.nextPeriod(self.settle, self.period))
    book.rootaccount=self.rootaccount.copy()
    book.settlerules=self.settlerules.copy()
    res=self.settlerules.run(book, self)
    if res: return (False, res)
    self.settled=1
    def undosettle(x):
      x.settled=1-x.settled
      return lambda: undosettle(x)
    return (True, book, lambda: undosettle(self))
  def loadInfo(self, data):
    self.set(data)
    return True
  def saveInfo(self):
    return self.get()
  def load(self, filename):
    with open(filename) as f:
      s=zlib.decompress(f.read())
      a, d, i, r=pickle.loads(s)
    rootaccount=RootAccount()
    deallist=DealList(rootaccount)
    settlerules=SettleRules()
    if not (rootaccount.load(a) and deallist.load(d)
      and self.loadInfo(i) and settlerules.load(r)): return False
    self.rootaccount=rootaccount
    self.deallist=deallist
    self.settlerules=settlerules
    return True
  def save(self, filename):
    with open(filename, 'w') as f:
      s=pickle.dumps((self.rootaccount.save(), self.deallist.save(),
        self.saveInfo(), self.settlerules.save()))
      f.write(zlib.compress(s))
    return True
  def tabdesc(self): # UI related.
    if self.valid(): return self.name
    else: return self.name+T(u' (invalid)')
  settle=property(lambda self: self.__settle, __setSettle)
  period=property(lambda self: self.__period, __setPeriod)

# UI module: Core
class Menu(object):
  # update: False->Not display True->Display
  def __init__(self, title=u'', target=None, update=None):
    self.target=target if target else lambda: None
    self.title=title if title else \
      self.target.title if self.isSubmenu() else u''
    self.update=update if update else \
      self.target.update if self.isSubmenu() else lambda: True
  def getItem(self):
    if self.isSubmenu():
      return (T(self.title), tuple(self.target.getItems()))
    else: return (T(self.title), self.target)
  def isSubmenu(self):
    return self.target.__class__ is MenuBar

class MenuBar(object):
  def __init__(self, title=u'', items=[]):
    self.title=title
    self.items=items
  def getItems(self):
    return [x.getItem() for x in self.items if x.update()]
  def append(self, item):
    self.items.append(item)
  def update(self):
    return any([x.update() for x in self.items])
  def popup(self):
    items=[x for x in self.items if x.update()]
    titles=[u'+'+T(x.title) if x.isSubmenu() else u'  '+T(x.title)
      for x in items]
    if len(titles)==0: return None
    while True:
      i=appuifw.popup_menu(titles, T(self.title))
      if i is None or i<0: return None
      item=items[i]
      if item.isSubmenu():
        ret=item.target.popup()
        if ret!=None: return ret
      else: return item

ETitle, EBody, EMenu, ETabs, EExit=0x01, 0x02, 0x04, 0x08, 0x10
EAll=0xff

class Window(object):
  def __init__(self):
    self.lock=None
  def run(self):
    self.lock=e32.Ao_lock()
    self.refresh()
    self.lock.wait()
    self.lock=None
    if hasattr(self, 'state'): return self.state
  def refresh(self, mask=EAll):
    if hasattr(self, 'update'): self.update(mask)
    if mask&ETitle and hasattr(self, 'title'):
      appuifw.app.title=self.title
    if mask&EBody and hasattr(self, 'body'):
      appuifw.app.body=self.body
    if mask&EMenu and hasattr(self, 'menu'):
      appuifw.app.menu=self.menu.getItems()
    if mask&ETabs:
      if hasattr(self, 'tabs'):
        if not hasattr(self, 'switch'): self.switch=None
        appuifw.app.set_tabs(self.tabs, self.switch)
        if not hasattr(self, 'tab'): self.tab=0
        appuifw.app.activate_tab(self.tab)
      else: appuifw.app.set_tabs([], None)
    if mask&EExit and hasattr(self, 'exit'):
      appuifw.app.exit_key_handler=self.exit
  def close(self):
    if self.lock: self.lock.signal()

class TopWindow(Window):
  def __init__(self, parent=None):
    Window.__init__(self)
    self.parent=parent
    self.subwindows=[]
  def refresh(self, mask=EAll):
    if self.subwindows: self.subwindows[0].refresh(mask)
    else: Window.refresh(self, mask)
  def add(self, window, top=False):
    if top: self.subwindows.insert(0, window)
    else: self.subwindows.append(window)
    if hasattr(self, 'handle_updateSubwindows'):
      self.handle_updateSubwindows()
  def remove(self, window):
    self.subwindows.remove(window)
    if hasattr(self, 'handle_updateSubwindows'):
      self.handle_updateSubwindows()
  def switchTo(self, index):
    if index==0: return
    win=self.subwindows[index]
    del self.subwindows[index]
    self.subwindows.insert(0, win)
    if hasattr(self, 'handle_updateSubwindows'):
      self.handle_updateSubwindows()
    self.refresh()
  def close(self):
    if not self.lock is None: self.lock.signal()
    else:
      self.parent.remove(self)
      self.parent.refresh()

class Property(object):
  # update: 0->Not display 1->Display
  #   2->Display but cannot get modified
  def __init__(self, value, desc, update=None):
    self.__value=value
    self.ovalue=value
    self.desc=desc
    self.update=update if update else lambda: 1
  def __setValue(self, value):
    self.__value=value
  def __getValue(self):
    if self.update(): return self.__value
    else: return self.ovalue
  def isModified(self):
    return self.value!=self.ovalue
  def listdesc(self):
    return (self.getName(), self.getValue())
  def getName(self):
    desc=self.desc
    if self.update()==2: desc+=u' (RO)'
    if self.isModified(): desc+=u' *'
    return desc
  def getValue(self):
    return unicode(self.value)
  def handle_reset(self):
    if self.isModified():
      self.value=self.ovalue
      return True
    else: return False
  value=property(__getValue, __setValue)
  # Need to implement "getValue", "handle_set".

class StrProperty(Property):
  def __init__(self, value, desc, update=None):
    Property.__init__(self, value, desc, update)
  def handle_set(self):
    res=appuifw.query(self.desc+u'?', u'text', self.value)
    if res==None or res==self.value: return False
    self.value=res
    return True

class BoolProperty(Property):
  def __init__(self, value, desc, update=None):
    Property.__init__(self, value, desc, update)
  def getValue(self):
    return EBool[1-self.value]
  def handle_set(self):
    res=appuifw.popup_menu(EBool, self.desc+u'?')
    if res==None or res!=self.value: return False
    self.value=1-res
    return True

class ChoiceProperty(Property):
  def __init__(self, value, desc, choices, update=None):
    Property.__init__(self, value, desc, update)
    self.choices=choices
  def getValue(self):
    if self.value<0 or self.value>=len(self.choices):
      return u'(invalid)'
    else: return self.choices[self.value]
  def handle_set(self):
    res=appuifw.popup_menu(self.choices, self.desc+u'?')
    if res==None or res==self.value: return False
    self.value=res
    return True

class TimeProperty(Property):
  def __init__(self, value, desc, update=None):
    Property.__init__(self, value, desc, update)
  def getValue(self):
    return T.Time(time.localtime(self.value))
  def handle_set(self):
    # TODO
    return True

class PropertyDialog(Window):
  def __init__(self):
    wp=weakref.proxy(self)
    Window.__init__(self)
    self.properties=[]
    self.body=appuifw.Listbox([(u'None', u'')],
      lambda: wp.handle_press())
    self.exit=lambda: wp.handle_exit()
  def append(self, property):
    self.properties.append(property)
    setattr(self, property.desc.replace(u' ', u'_'), property)
  def get(self):
    return tuple([i.value for i in self.properties])
  def isModified(self):
    return any([i.isModified() for i in self.properties])
  def valid(self):
    return True
  def update(self, mask):
    wp=weakref.proxy(self)
    if mask&ETitle:
      self.handle_title()
    if mask&EBody:
      self.actives=[i for i in self.properties if i.update()]
      lists=[i.listdesc() for i in self.actives]
      self.body.set_list(lists, self.body.current())
      self.body.bind(key_codes.EKeyBackspace,
        lambda: wp.handle_delete())
  def handle_press(self):
    property=self.actives[self.body.current()]
    if property.update()==1 and property.handle_set():
      self.refresh()
  def handle_delete(self):
    property=self.actives[self.body.current()]
    if property.update()==1 and property.handle_reset():
      self.refresh()
  def handle_title(self):
    self.title=u''
  # state: 0->not save 1->save
  def handle_exit(self):
    if self.isModified():
      if self.valid():
        res=appuifw.popup_menu(EChange, u'Changes')
        if res==1: self.state=0
        elif res==0: self.state=1
        else: return
      else:
        res=appuifw.query(u'Exit without saving?', u'query')
        if not res: return
        else: self.state=0
    else: self.state=0
    self.close()

# UI module: Functions
def mycmp(str1, str2):
  i=0
  while i<len(str1) and i<len(str2):
    a, b=ord(str1[i]), ord(str2[i])
    if a>=65 and a<=90: a+=32
    if b>=65 and b<=90: b+=32
    if a!=b:
      if a<b: return -1
      else: return 1
    i+=1
  if len(str1)!=len(str2):
    if len(str1)<len(str2): return -1
    else: return 1
  return 0

def choosePath(defaultdir=u''):
  dirs=[i for i in defaultdir.split(u'\\') if i]
  while(1):
    if not dirs:
      list=e32.drive_list()
      choice=appuifw.popup_menu(list, T(u'Path:'))
      if choice==None: return None
      dirs.append(list[choice])
    else:
      dir=u'\\'.join(dirs)
      list=[i for i in os.listdir(dir) if os.path.isdir(dir+u'\\'+i)]
      list.sort(mycmp)
      names=[u'['+i+u']' for i in list]
      names.insert(0, u' ..')
      names.insert(0, T(u'>>> Here <<<'))
      choice=appuifw.popup_menu(names, T(u'Path:')+u' '+dir)
      if choice==None: return None
      if choice==0: return dir
      if choice==1: dirs.pop()
      else: dirs.append(list[choice-2])

def chooseFile(defaultdir=u'', extension=u''):
  dirs=[i for i in defaultdir.split(u'\\') if i]
  if dirs and not os.path.isdir(defaultdir):
    dirs.pop()
  while(1):
    if not dirs:
      list=e32.drive_list()
      choice=appuifw.popup_menu(list, T(u'Path:'))
      if choice==None: return None
      dirs.append(list[choice])
    else:
      dir=u'\\'.join(dirs)
      list=os.listdir(dir)
      list.sort(mycmp)
      list1, list2, names, names2=[], [], [], []
      names.append(u' ..')
      for i in list:
        if os.path.isdir(dir+u'\\'+i):
          names.append(u'['+i+u']')
          list1.append(i)
        elif i.endswith(extension):
          names2.append(i)
          list2.append(i)
      list=list1+list2
      names+=names2
      choice=appuifw.popup_menu(names, T(u'Path:')+u' '+dir)
      if choice==None: return None
      if choice==0: dirs.pop()
      elif os.path.isdir(dir+'\\'+list[choice-1]):
        dirs.append(list[choice-1])
      else: return dir+'\\'+list[choice-1]

def chooseFinalAccount(account):
  while(1):
    list=account.items
    names=[i.tabdesc() for i in list]
    if not account.isRoot(): names.insert(0, u'  ..')
    choice=appuifw.popup_menu(names,u'Account: '+
      account.getFullname())
    if choice==None: return None
    if account.isRoot():
      if list[choice].placeholder: account=list[choice]
      else: return list[choice]
    elif choice==0: account=account.parent
    elif not list[choice-1].placeholder: return list[choice-1]
    else: account=list[choice-1]

def chooseParentAccount(account):
  while(1):
    list=account.items
    places=[i for i in list if i.placeholder]
    names=[i.name for i in places]
    if not account.isRoot():
      names.insert(0, u'  ..')
    names.insert(0, u'>>> Here <<<')
    choice=appuifw.popup_menu(names, u'Place: '+
      account.getFullname())
    if choice==None: return None
    if choice==0: return account
    if account.isRoot(): account=places[choice-1]
    elif choice==1: account=account.parent
    else: account=places[choice-2]

# UI module: Main
class ParentProperty(Property):
  def __init__(self, parent, dialog):
    Property.__init__(self, parent, u'Parent')
    self.dialog=dialog
    self.account=dialog.account
  def getValue(self):
    return self.value.getFullname()
  def handle_set(self):
    res=chooseParentAccount(self.value)
    if res is None or res==self.value: return False
    if self.account and self.account.isParent(res):
      appuifw.note(T(u'Loop! Cannot move!'), u'error')
      return False
    self.value=res
    if not res.isRoot():
      self.dialog.Type.value=res.type
    self.dialog.Position.value=0
    return True
  def handle_reset(self):
    if self.isModified:
      self.value=self.ovalue
      if not self.value.isRoot():
        self.dialog.Type.value=self.value.type
      if self.dialog.Position.value>self.dialog.Position.max:
        self.dialog.Position.value=self.dialog.Position.ovalue
      return True
    else: return False

class PosProperty(Property):
  def __init__(self, pos, dialog):
    wp=weakref.proxy(self)
    Property.__init__(self, pos, u'Position',
      update=lambda: 2 if wp.max==0 else 1)
    self.dialog=dialog
    self.account=dialog.account
  def getValue(self):
    return unicode(self.value+1)
  def handle_set(self):
    max=self.max
    res=appuifw.query(u'Position (1~'+unicode(max+1)+u')?',
      u'number', self.value+1)
    if res==None or res-1==self.value: return False
    if res<1 or res>max+1:
      appuifw.note(u'Invalid position!', u'error')
      return False
    self.value=res-1
    return True
  def handle_reset(self):
    max=self.max
    if self.ovalue>max: return False
    if self.isModified():
      self.value=self.ovalue
      return True
    else: return False
  def __getMax(self):
    if self.account and \
        self.account.parent is self.dialog.Parent.value:
      return len(self.dialog.Parent.value.items)-1
    else: return len(self.dialog.Parent.value.items)
  max=property(__getMax)

class AccountDialog(PropertyDialog):
  def __init__(self, data, account=None):
    wp=weakref.proxy(self)
    PropertyDialog.__init__(self)
    self.account=account
    self.append(StrProperty(data[0], u'Name'))
    self.append(StrProperty(data[1], u'Description'))
    self.append(ChoiceProperty(data[2], u'Type', EAccountType,
      lambda: 1 if wp.Parent.value.isRoot() else 2))
    self.append(BoolProperty(data[3], u'Placeholder',
      lambda: 2 if account and len(account.items) else 1))
    self.append(ParentProperty(data[4], wp))
    self.append(PosProperty(data[5], wp))
    self.menu=MenuBar(T(u'Menu'), [
      Menu(u'Clear name', lambda: wp.handle_clearname(),
        lambda: wp.Name.value),
      Menu(u'Clear description', lambda: wp.handle_cleardesc(),
        lambda: wp.Description.value),
      Menu(u'Exit', lambda: wp.handle_exit())])
  def valid(self):
    return Account.validData(self.get())
  def handle_clearname(self):
    self.Name.value=u''
    self.refresh()
  def handle_cleardesc(self):
    self.Description.value=u''
    self.refresh()
  def handle_title(self):
    tab=self.Name.value
    if self.Placeholder.value: tab+=u' +'
    if self.isModified(): tab+=u' *'
    if not self.valid(): tab+=T(u' (invalid)')
    self.title=tab

class AmountProperty(Property):
  def __init__(self, amount, dialog):
    Property.__init__(self, amount, u'Amount')
    self.dialog=dialog
  def getValue(self):
    return u'%5.2f\xa5'%self.value
  def handle_set(self):
    res=appuifw.query(u'Amount?', u'float', self.value)
    if res is None: return False
    res=round(res, 2)
    if res==self.value: return False
    if res<0.0 :
      self.value=-res
      self.dialog.exchangeAccounts()
    else: self.value=res
    return True

class FrToProperty(Property):
  def __init__(self, account, type, dialog):
    Property.__init__(self, account, EFromTo[type])
    self.type=type
    self.dialog=dialog
  def getName(self):
    lable=EItemType[self.type]
    if self.value:
      lable+=u' (+)' if EDeal[self.type][self.value.type]>0 \
        else u' (-)'
    if self.isModified(): lable+=u' *'
    return lable
  def getValue(self):
    return self.value.getFullname() if self.value else u'(invalid)'
  def handle_set(self):
    if self.value: res=chooseFinalAccount(self.value.parent)
    else: res=chooseFinalAccount(self.dialog.rootaccount)
    if res is None or res is self.value: return False
    if res is getattr(self.dialog, EFromTo[1-self.type]).value:
      appuifw.note(u'The same to the "'+EItemType[1-self.type]+
        '" account!', u'error')
      return False
    self.value=res
    return True
  def handle_reset(self):
    if self.isModified():
      other=getattr(self.dialog, EFromTo[1-self.type])
      if self.ovalue and self.ovalue is other.value:
        if other.ovalue is self.value:
          self.dialog.exchangeAccounts()
          return True
        return False
      self.value=self.ovalue
      return True
    else: return False

class DealDialog(PropertyDialog):
  def __init__(self, data, rootaccount):
    # data: amount desc from to time
    PropertyDialog.__init__(self)
    wp=weakref.proxy(self)
    self.rootaccount=rootaccount
    self.append(AmountProperty(data[0], wp))
    self.append(StrProperty(data[1], u'Description'))
    self.append(FrToProperty(data[2], EFrom, wp))
    self.append(FrToProperty(data[3], ETo, wp))
    self.append(TimeProperty(data[4], u'Time', lambda: 2))
    self.menu=MenuBar(T(u'Menu'), [
      Menu(u'Clear description', lambda: wp.handle_cleardesc(),
        lambda: len(wp.Description.value)),
      Menu(u'Exchange Accounts', lambda: wp.handle_exchange()),
      Menu(u'Exit', lambda: wp.handle_exit())])
  def valid(self):
    return Deal.validData(self.get())
  def exchangeAccounts(self):
      temp=self.From.value
      self.From.value=self.To.value
      self.To.value=temp
  def handle_cleardesc(self):
    self.Description.value=u''
    self.refresh()
  def handle_exchange(self):
    self.exchangeAccounts()
    self.refresh()
  def handle_title(self):
    tab=self.Description.value
    if self.isModified(): tab+=u' *'
    if not self.valid(): tab+=T(u' (invalid)')
    self.title=tab

class UndoRedoDialog(Window):
  def __init__(self, undoredo, bookname):
    wp=weakref.proxy(self)
    Window.__init__(self)
    self.undoredo=undoredo
    self.title=bookname+u' Undo&Redo Panel'
    self.body=appuifw.Listbox([u'None'],
      lambda: wp.handle_press())
    self.exit=lambda: wp.close()
    self.menu=MenuBar(u'Menu', [
      Menu(u'Clear', lambda: wp.handle_clear(),
        lambda: wp.undoredo.undolist or wp.undoredo.redolist),
      Menu(u'Exit', lambda: wp.exit())])
  def update(self, mask):
    if mask&EBody:
      lists=[u'   '+i[1] for i in self.undoredo.undolist]
      lists.append(u'   >>>    Current    <<<')
      lists+=[u'   '+i[1] for i in reversed(self.undoredo.redolist)]
      if not self.undoredo.modified is None:
        index=len(self.undoredo.undolist)-self.undoredo.modified
        lists[index]=u'* '+lists[index][3:]
      self.body.set_list(lists, self.body.current())
  def handle_clear(self):
    self.undoredo.clear()
    self.refresh()
  def handle_press(self):
    self.undoredo.go(len(self.undoredo.undolist)-
      self.body.current())
    self.refresh()

class SettleProperty(Property):
  def __init__(self, settle, dialog):
    Property.__init__(self, settle, u'Settlement and Duration')
    self.dialog=dialog
  def getValue(self):
    return ESettle[self.value]
  def handle_set(self):
    res=appuifw.popup_menu(ESettle, self.desc+u'?')
    if res==None or res==self.value: return False
    self.value=res
    self.dialog.Period.value=self.dialog.Period.getDefault()
    self.dialog.Settled.value=0
    return True
  def handle_reset(self):
    if self.isModified():
      self.value=self.ovalue
      self.dialog.Period.value=self.dialog.Period.getDefault()
      self.dialog.Settled.value=0
      return True
    else: return False

class PeriodProperty(Property):
  def __init__(self, period, dialog):
    wp=weakref.proxy(self)
    Property.__init__(self, period, u'Period',
      lambda: wp.settle.value!=ESettleNone)
    self.dialog=dialog
  def getName(self):
    if self.settle.value==ESettleByMonth: desc=u'Month'
    else:
      assert self.settle.value==ESettleBySeason
      desc=u'Season'
    if self.isModified(): desc+=u' *'
    return desc
  def getDefault(self):
    return Book.parsePeriod(self.settle.value, self.time.value)
  def getValue(self):
    if self.settle.value==ESettleByMonth:
      return EMonth[self.value[1]]+u' in '+unicode(self.value[0])
    else:
      assert self.settle.value==ESettleBySeason
      return u'The '+EOrdinal[self.value[1]]+u' season in '+\
        unicode(self.value[0])
  def isModified(self):
    if self.settle.isModified(): return self.value!=self.getDefault()
    else: return self.value!=self.ovalue
  def handle_set(self):
    if self.settle.value==ESettleByMonth:
      f=appuifw.popup_menu(EMonth[1:], u'Month?')
    else:
      f=appuifw.popup_menu([u'The '+i+u' season'
        for i in EOrdinal[1:]], u'Season?')
    if f==None: return False
    s=appuifw.query(u'Year?', u'number', self.value[0])
    if s==None or self.value==(s, f+1): return False
    self.value=(s, f+1)
    self.dialog.Settled.value=0
    return True
  def handle_reset(self):
    if not self.isModified(): return False
    if self.settle.isModified(): self.value=self.getDefault()
    else: self.value=self.ovalue
    self.dialog.Settled.value=0
    return True
  settle=property(
    lambda self: self.dialog.Settlement_and_Duration)
  time=property(lambda self: self.dialog.Creation_Time)

class SettledProperty(BoolProperty):
  def __init__(self, settled, dialog):
    wp=weakref.proxy(self)
    BoolProperty.__init__(self, settled, u'Settled',
      lambda: 0 if wp.settle.value==ESettleNone else 1)
    self.dialog=dialog
  def isToBeSettled(self):
    return Book.isToBeSettled(self.settle.value, self.period.value)
  def getName(self):
    desc=self.desc
    if self.isToBeSettled(): desc+=u' (To be settled)'
    return desc
  settle=property(
    lambda self: self.dialog.Settlement_and_Duration)
  period=property(lambda self: self.dialog.Period)

class BookDialog(PropertyDialog):
  def __init__(self, data):
    wp=weakref.proxy(self)
    PropertyDialog.__init__(self)
    self.append(StrProperty(data[0], u'Name'))
    self.append(StrProperty(data[1], u'Description'))
    self.append(TimeProperty(data[2], u'Creation Time',
      lambda: 2))
    self.append(SettleProperty(data[3], wp))
    self.append(PeriodProperty(data[4], wp))
    self.append(SettledProperty(data[5], wp))
    self.menu=MenuBar(T(u'Menu'), [
      Menu(u'Clear name', lambda: wp.handle_clearname(),
        lambda: wp.Name.value),
      Menu(u'Clear description', lambda: wp.handle_cleardesc(),
        lambda: wp.Description.value),
      Menu(u'Exit', lambda: wp.handle_exit())])
  def valid(self):
    return Book.validData(self.get())
  def handle_clearname(self):
    self.Name.value=u''
    self.refresh()
  def handle_cleardesc(self):
    self.Description.value=u''
    self.refresh()
  def handle_title(self):
    tab=self.Name.value
    if self.isModified(): tab+=u' *'
    if not self.valid(): tab+=T(u' (invalid)')
    self.title=tab

class StrRuleProperty(StrProperty):
  def __init__(self, rule, name):
    StrProperty.__init__(self, rule, name)

class TestProperty(object):
  def __init__(self):
    self.handle_test()
  def isModified(self):
    return False
  def update(self):
    return 1
  def handle_reset(self):
    return False
  def listdesc(self):
    if self.result[0]: desc=self.result[1]
    else: desc=u'(invalid)'
    return (u'Test', desc)
  def handle_test(self):
    return (True, u'')
  def handle_set(self):
    if result[0]: appuifw.note(self.result[1], u'info')
    else: appuifw.note(self.result[1], u'error')
    return False

class __RuleDialog(PropertyDialog):
  def __init__(self, name, desc, rules, test):
    wp=weakref.proxy(self)
    PropertyDialog.__init__(self)
    self.rules=rules
    self.append(StrProperty(desc, u'Description'))
    for i in rules:
      self.append(i)
    self.append(test)
    self.menu=MenuBar(T(u'Menu'), [
      Menu(u'Clear description', lambda: wp.handle_cleardesc(),
        lambda: wp.Description.value),
      Menu(u'Exit', lambda: wp.handle_exit())])
  def get(self):
    return tuple([self.Description.value]+
      [i.value for i in self.rules])
  def valid(self):
    return True
  def handle_cleardesc(self):
    self.Description.value=u''
    self.refresh()
  def handle_title(self):
    tab=self.name+u': '+self.Descripition.value
    if self.isModified(): tab+=u' *'
    if not self.valid(): tab+=T(u' (invalid)')

class NameRuleTest(TestProperty):
  def __init__(self, rule, book):
    self.rule=rule
    self.book=book
    TestProperty.__init__(self)
  def handle_test(self):
    self.result=NameRule.test(self.rule.rule, self.book)

class __NameDialog(__RuleDialog):
  def __init__(self, book):
    self.book=book
    namerule=self.book.settlerules.namerule
    rule=StrRuleProperty(namerule.rule, 'Rule')
    __RuleDialog.__init__(self, 'Name Rule',namerule.desc, [
      rule])

class RuleDialog(Window):
  def __init__(self, desc, rule, name):
    wp=weakref.proxy(self)
    Window.__init__(self)
    self.desc=desc
    self.rule=self.orule=rule
    self.name=name
    self.data={}
    self.menu=MenuBar(T(u'Menu'), [
      Menu(u'Clear rule', lambda: wp.handle_clearrule()),
      Menu(u'Sample data', lambda: wp.handle_data()),
      Menu(u'Exit', lambda: wp.handle_exit())])
    self.body=appuifw.Listbox([(u'None', u'')],
      lambda: wp.handle_press())
    self.exit=lambda: wp.handle_exit()
  def __setRule(self, rule):
    self.__rule=rule
    self.test=self.handle_test()
  def getTest(self):
    if self.valid(): return self.test
    else: return u'(invalid)'
  def isModified(self):
    return self.rule!=self.orule
  def valid(self):
    return not (self.test is None)
  def update(self, mask):
    wp=weakref.proxy(self)
    if mask&ETitle:
      self.handle_title()
    if mask&EBody:
      if self.isModified(): lists=[(u'Rule *', self.rule)]
      else: lists=[(u'Rule', self.rule)]
      lists.append((u'Test resule', self.getTest()))
      self.body.set_list(lists, self.body.current())
      self.body.bind(key_codes.EKeyBackspace,
        lambda: wp.handle_reset())
  def handle_press(self):
    current=self.body.current()
    if current==0:
      res=appuifw.query(self.name+u'?', u'text', self.rule)
      if res==None or res.strip()==self.rule: return
      self.rule=res.strip()
      self.refresh()
    elif current==1 and not self.valid():
      appuifw.note(self.error, u'error')
  def handle_clearrule(self):
    self.rule=u''
    self.refresh()
  def handle_reset(self):
    if not self.isModified(): return
    self.rule=self.orule
    self.refresh()
  def handle_title(self):
    tab=self.name
    if self.isModified(): tab+=u' *'
    if not self.valid(): tab+=T(u' (invalid)')
    self.title=tab
  def handle_data(self):
    def process(d):
      if type(d) is unicode:
        return unicode(repr(d)[:2])+d+unicode(repr(d)[-1])
      else: return unicode(repr(d))
    lists=[i[0]+u' = '+process(i[1]) for i in self.data]
    while True:
      res=appuifw.popup_menu(lists, u'Sample data:')
      if res is None: return
      appuifw.query(self.data[res][0]+u' =', u'text',
        process(self.data[res][1]))
  def handle_test(self):
    # Implemented by the derived class.
    # return: None->invalid Unicode->okay
    pass
  def handle_exit(self):
    if self.isModified():
      if self.valid():
        res=appuifw.popup_menu(EChange, u'Changes')
        if res==1: self.state=0
        elif res==0: self.state=1
        else: return
      else:
        res=appuifw.query(u'Exit without saving?', u'query')
        if not res: return
        else: self.state=0
    else: self.state=0
    self.close()
  rule=property(lambda self: self.__rule, __setRule)

class NameRuleDialog(RuleDialog):
  def __init__(self, book):
    self.book=book
    rule=book.settlerules.namerule
    RuleDialog.__init__(self, rule.desc, rule.rule,
      u'Name Rule')
    self.data=NameRule.getDict(book).items()
  def handle_test(self):
    result=NameRule.test(self.rule, self.book)
    if result[0]: return result[1]
    else: self.error=result[1]

class DescRuleDialog(RuleDialog):
  def __init__(self, book):
    self.book=book
    rule=book.settlerules.descrule
    RuleDialog.__init__(self, rule.desc, rule.rule,
      u'Descripition Rule')
    self.data=DescRule.getDict(book).items()
  def handle_test(self):
    result=DescRule.test(self.rule, self.book)
    if result[0]: return result[1]
    else: self.error=result[1]

class RulesDialog(Window):
  def __init__(self, book, undoredo):
    wp=weakref.proxy(self)
    Window.__init__(self)
    self.book=book
    self.undoredo=undoredo
    self.menu=MenuBar(T(u'Menu'), [
      Menu(u'Exit', lambda: wp.handle_exit())])
    self.body=appuifw.Listbox([(u'None', u'')],
      lambda: wp.handle_press())
    self.exit=lambda: wp.handle_exit()
  def update(self, mask):
    wp=weakref.proxy(self)
    if mask&ETitle:
      self.title=T(u'Rules')
    if mask&EBody:
      self.handle_body()
  def handle_body(self):
    lists=[(u'Name Rule', self.namerule.desc),
      (u'Descripition Rule', self.descrule.desc)]
    for i in range(0, len(self.dealrules)):
      lists.append((u'Deal Rule '+unicode(i+1),
        self.dealrules[i].desc))
    self.body.set_list(lists, self.body.current())
  def handle_press(self):
    index=self.body.current()
    if index==0:
      d=NameRuleDialog(self.book)
      if d.run():
        self.undoredo.append(self.namerule.set((d.rule,)),
          u'Edit Name Rule')
    elif index==1:
      d=DescRuleDialog(self.book)
      if d.run():
        self.undoredo.append(self.descrule.set((d.rule,)),
          u'Edit Descripition Rule')
    else: return
    self.refresh()
  def handle_delete(self):
    pass
  def handle_exit(self):
    self.close()
  namerule=property(
    lambda self: self.book.settlerules.namerule)
  descrule=property(lambda self: self.book.settlerules.descrule)
  dealrules=property(
    lambda self: self.book.settlerules.dealrules)

class AccountWindow(TopWindow):
  def __init__(self, parent, book, account=None, filename=u''):
    wp=weakref.proxy(self)
    TopWindow.__init__(self, parent)
    self.book=book
    self.account=account if account else book.rootaccount
    self.filename=filename
    self.undoredo=UndoRedo()
    if not filename: self.undoredo.modified=None
    self.fileMenu=MenuBar(T(u'File'), [
      Menu(u'New', lambda: wp.parent.handle_new()),
      Menu(u'Open...', lambda: wp.parent.handle_open()),
      Menu(u'Save', lambda: wp.handle_save(),
        lambda: wp.filename),# and wp.undoredo.isModified()
      Menu(u'Save as...', lambda: wp.handle_saveas())])
    self.editMenu=MenuBar(u'Edit', [
      Menu(u'Add account...', lambda: wp.handle_additem(),
        lambda: wp.account.placeholder),
      Menu(u'Add Deal...', lambda: wp.handle_additem(),
        lambda: not wp.account.placeholder),
      Menu(u'Del account', lambda: wp.handle_delitem(),
        lambda: wp.account.placeholder and wp.account.items),
      Menu(u'Del Deal', lambda: wp.handle_delitem(),
        lambda: not wp.account.placeholder and
        wp.account.items),
      Menu(u'Undo', lambda: wp.handle_undo(),
        lambda: wp.undoredo.hasUndo()),
      Menu(u'Redo', lambda: wp.handle_redo(),
        lambda: wp.undoredo.hasRedo()),
      Menu(u'Undo&Redo...',
        lambda: wp.handle_undoredo(),
        lambda: wp.undoredo.undolist or wp.undoredo.redolist)])
    self.propertyMenu=MenuBar(u'Property', [
      Menu(u'Account...', lambda: wp.handle_property(),
        lambda: wp.account.items and wp.account.placeholder),
      Menu(u'Deal...', lambda: wp.handle_property(),
        lambda: wp.account.items and
        not wp.account.placeholder),
      Menu(u'Book...', lambda: wp.handle_book()),
      Menu(u'Rules...', lambda: wp.handle_rules())])
    self.menu=MenuBar(u'Menu', [
      Menu(target=self.fileMenu),
      Menu(target=self.editMenu),
      Menu(target=self.propertyMenu),
      Menu(target=self.parent.windowsMenu),
      Menu(u'Settle', lambda: wp.handle_settle()),
      Menu(u'Exit', lambda: wp.handle_exit())])
    self.index=0
    self.body=appuifw.Listbox([(u'None', u'')],
      lambda: wp. handle_press())
    self.exit=lambda: wp.handle_exit()
  def update(self, mask):
    wp=weakref.proxy(self)
    # e.g. when enter an account after "undo" deleting the
    #   account and then "redo"
    if not self.account.established:
      self.account=self.book.rootaccount
    if mask&ETitle:
      if self.account.isRoot():
        self.title=self.book.name+u' %5.2f\xa5'% \
          self.book.rootaccount.sum
        if self.undoredo.isModified(): self.title+=u' *'
      else: self.title=self.account.getFullname()
    if mask&EBody:
      lists=[i.listdesc() for i in self.account.items]
      if len(lists)==0: lists=[(u'(None)', u'')]
      if self.index is None:
        self.body.set_list(lists, self.body.current())
      else:
        self.body.set_list(lists, self.index)
        self.index=None
      self.body.bind(key_codes.EKeyBackspace,
        lambda: wp.handle_delitem())
    if mask&ETabs:
      if not self.account.isRoot():
        self.tabs=[i.tabdesc() for i in self.account.parent.items]
        self.tab=self.account.parent.items.index(self.account)
      else:
        self.tabs=[]
        self.tab=0
  def handle_exit(self):
    if not self.account.isRoot():
      self.account=self.account.parent
      self.index=self.tab
      self.refresh()
    else:
      if self.undoredo.isModified():
        res=appuifw.popup_menu(EChange, u'Changes')
        if res==0:
          if not self.handle_save(): return
        elif res is None: return
      self.close()
  def switch(self, index):
    self.account=self.account.parent.items[index]
    self.tab=index
    self.refresh(ETitle|EBody|EMenu)
  def handle_press(self):
    if not self.account.items: return
    index=self.body.current()
    if self.account.placeholder:
      self.account=self.account.items[index]
      self.index=0
      self.refresh()
    else: self.handle_property()
  def handle_undoredo(self):
    UndoRedoDialog(self.undoredo, self.book.name).run()
    self.refresh()
  def handle_property(self):
    index=self.body.current()
    item=self.account.items[index]
    if self.account.placeholder:
      a=AccountDialog(item.get(), item)
      if a.run():
        self.undoredo.append(item.set(a.get()),
          u'Edit Account "%s"'%(item.name))
    else:
      d=DealDialog(item.deal.get(), self.book.rootaccount)
      if d.run():
        self.undoredo.append(item.deal.set(d.get()),
          u'Edit Deal "%s"'%(item.deal.desc))
    self.refresh()
  def handle_book(self):
    b=BookDialog(self.book.get())
    if b.run():
      self.undoredo.append(self.book.set(b.get()),
        u'Edit Book Property')
    self.refresh()
  def handle_rules(self):
    #r=RuleDialog(self.book.settlerules.get())
    #if r.run():
    #  self.undoredo.append(self.book.settlerules.set(r.get()),
    #    u'Edit Settle Rule')
    RulesDialog(self.book, self.undoredo).run()
    self.refresh()
  def handle_additem(self):
    if self.account.placeholder:
      a=AccountDialog((u'', u'', self.account.type, 0, self.account,
        self.body.current()))
      if a.run():
        account=Account(self.book.rootaccount, *a.get())
        self.undoredo.append(account.establish(1),
          u'Add Account "%s"'%(account.name))
    else:
      d=DealDialog((0.0, u'', None, self.account, time.time()),
        self.book.rootaccount)
      if d.run():
        deal=Deal(self.book.deallist, *d.get())
        self.undoredo.append(deal.establish(1),
          u'Add Deal "%s"'%(deal.desc))
    self.refresh()
  def handle_delitem(self):
    if not self.account.items: return
    index=self.body.current()
    item=self.account.items[index]
    if self.account.placeholder:
      if len(item.items):
        res=appuifw.query(T(u'The data in the account '
          u'will also be deleted.\nContinue?'), u'query')
        if res!=True: return
      funclist=[item.clear()]
      funclist.append(item.establish(0))
      funclist.reverse()
      func=MergeFunc(funclist)
      self.undoredo.append(func,
        u'Delete Account "%s"'%(item.name))
    else:
      self.undoredo.append(item.deal.establish(0),
        u'Delete Deal "%s"'%(item.deal.desc))
    self.refresh()
  def handle_undo(self):
    self.undoredo.undo()
    self.refresh()
  def handle_redo(self):
    self.undoredo.redo()
    self.refresh()
  def handle_settle(self):
    if self.book.settled:
      res=appuifw.query(u'The book is marked to '
        u'have been settled.\nContinue?', u'query')
      if not res: return
      settled=1
    else: settled=0
    result=self.book.doSettle()
    if not result[0]:
      appuifw.note(result[1], u'error')
      return
    book, func=result[1:]
    if not settled:
      self.undoredo.append(func, u'Settle the book')
    if not book.valid():
      b=BookDialog(book.get())
      if not b.run():
        self.refresh()
        return
      book.set(b.get())
    self.parent.add(AccountWindow(self.parent, book), True)
    self.parent.refresh()
  def handle_save(self):
    if self.filename:
      if self.book.save(self.filename):
        self.undoredo.resetModified()
        self.refresh()
        appuifw.note(T(u'File save to "%s".')%self.filename,
          u'conf')
        return True
      else:
        appuifw.note(u'Fail to save.', u'error')
        return False
    else: return self.handle_saveas()
  def handle_saveas(self):
    if self.filename:
      dedir, dename=os.path.split(self.filename)
    else:
      dedir=u''
      dename=self.book.name
    path=choosePath(dedir)
    if not path: return False
    filename=appuifw.query(u'Filename (*.cash)?', u'text',
      dename)
    if not filename: return False
    if not filename.endswith(u'.cash'): filename+=u'.cash'
    if self.book.save(path+u'\\'+filename):
      self.filename=path+u'\\'+filename
      self.undoredo.resetModified()
      self.refresh()
      appuifw.note(T(u'File save to "%s".')%self.filename, u'conf')
      return True
    else:
      appuifw.note(u'Fail to save.', u'error')
      return False

class RootWindow(TopWindow):
  def __init__(self):
    wp=weakref.proxy(self)
    TopWindow.__init__(self)
    self.title=u'Cash'
    self.fileMenu=MenuBar(u'File', [
      Menu(u'New', lambda: wp.handle_new()),
      Menu(u'Open...', lambda: wp.handle_open())])
    self.windowsMenu=MenuBar(u'Windows', [])
    self.menu=MenuBar(u'Menu', [
      Menu(target=self.fileMenu),
      Menu(target=self.windowsMenu),
      Menu(u'Exit', lambda: wp.close())])
    self.popupmenu=MenuBar(u'Context Menu', [
      Menu(u'Open...', lambda: wp.handle_open()),
      Menu(u'New', lambda: wp.handle_new())])
    self.body=appuifw.Canvas(
      redraw_callback=lambda area: wp.handle_redraw(area),
      event_callback=lambda event: wp.handle_event(event))
    self.exit=lambda: wp.close()
    self.image=graphics.Image.new(self.body.size)
    self.text=EBanner
    self.font=(u'Sans MT 936_S60', 18, graphics.FONT_ANTIALIAS)
    self.outline=0x5f5f5f
    self.background=0xffffff
    self.redraw()
  def redraw(self):
    self.image.clear(self.background)
    x, y=10, 30
    for ln in self.text:
      if ln==u'-':
        self.image.line((x, y-9, self.body.size[0]-x, y-9),
          outline=self.outline)
      elif ln:
        self.image.text((x, y), ln, fill=self.outline, font=self.font)
      y+=23
  def handle_updateSubwindows(self):
    wp=weakref.proxy(self)
    items=[]
    def mkswitch(i):
      return lambda: wp.switchTo(i)
    for i in range(1, len(self.subwindows)):
      items.append(Menu(self.subwindows[i].book.name,
        mkswitch(i)))
    self.windowsMenu.items=items
  def handle_redraw(self, area):
    self.body.blit(self.image)
  def handle_event(self, event):
    if event['type']==appuifw.EEventKey:
      code=event['scancode']
      if code==key_codes.EScancodeSelect:
        self.handle_press()
  def handle_press(self):
    res=self.popupmenu.popup()
    if res: res.target()
  def handle_new(self):
    b=BookDialog((u'', u'', time.time(), ESettleNone, None,0))
    if b.run():
      book=Book(*b.get())
      self.add(AccountWindow(self, book), True)
    self.refresh()
  def handle_open(self):
    res=chooseFile(u'', u'.cash')
    if not res: return
    filenames=[i.filename for i in self.subwindows]
    if res in filenames:
      self.switchTo(filenames.index(res))
      self.refresh()
      return      
    book=Book()
    if book.load(res):
      self.add(AccountWindow(self, book, filename=res), True)
      self.refresh()
    else: appuifw.note(u'Bad file format.', u'error')

class Notify(object):
  def __init__(self, position=(0,0)):
    self.image=graphics.Image.new((30,30))
    self.win=topwindow.TopWindow()
    self.win.add_image(self.image, (0,0))
    self.show=False
    self.font=(u'Sans MT 936_S60', 18, 16)
    self.text=[]
    self.position=position
  def __getSize(self):
    return self.win.size
  def refresh(self, text):
    box, _, _=self.image.measure_text(text=text, font=self.font)
    size=(box[2]+3, -box[1]+7)
    self.win.remove_image(self.image)
    self.image=graphics.Image.new(size)
    self.image.text((1,size[1]-1), text=text, font=self.font)
    self.image.rectangle((0,0, size[0],size[1]), outline=0)
    self.win.size=size
    self.win.add_image(self.image, (0,0))
  def __setPosition(self, position):
    self.win.position=position
  def update(self):
    if len(self.text):
      self.show=True
      self.refresh(self.text[0])
      del self.text[0]
      self.win.show()
      e32.ao_sleep(0.2, self.update)
    else:
      self.show=False
      self.win.hide()
  def notify(self, text):
    self.text.append(text)
    if not self.show: self.update()
    e32.ao_yield()
  size=property(lambda self: self.win.size)
  position=property(lambda self: self.win.position, __setPosition)

#with open('E:\\log.txt', 'w') as log:
#log.write('Start Garbage Number: '+str(gc.collect())+'\n')
RootWindow().run()
#log.write('End Garbage Number: '+str(gc.collect())+'\n')
