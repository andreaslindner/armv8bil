#!/usr/bin/python

import sys
import re


# read all parameters
if len(sys.argv) < (3 + 1):
  print "too few arguments, exiting."
  print "Usage: exportfun.py dumpfile funname output.ml"
  sys.exit()


dumpfile   = sys.argv[1]
funname    = sys.argv[2]
outfile    = sys.argv[3]


# read everything from inputfile
with open(dumpfile) as f:
  content = f.readlines()


# parse input data
#------------- https://docs.python.org/2/library/re.html
interesting_line = False
linecount = 0
first_addr = ""
pattern_start = re.compile("^\s*(?P<addr>[0-9a-f]+) <" + funname + ">:.*$")
pattern_stop  = re.compile("^\s*[0-9a-f]+ <.*>:.*$")
pattern_asmbl = re.compile("^\s*(?P<addr>[0-9a-f]+):\s+(?P<instr>[0-9a-f]+)\s+.*$")
mlarray = ""
# line by line
for line in content:
  m_start = pattern_start.match(line)
  if m_start:
    interesting_line = True
    first_addr_start = m_start.group("addr")
  elif pattern_stop.match(line):
    interesting_line = False
  elif interesting_line:
    m = pattern_asmbl.match(line)
    if m:
      linecount += 1
      if not first_addr:
        first_addr = m.group("addr")
      last_addr = m.group("addr")
      mlarray += '"%s",' % m.group("instr")
      if linecount % 7 == 0:
        mlarray += "\n"
    elif not line.strip():
      continue
    else:
      print "cannot parse the following line, exiting."
      print line
      sys.exit()



# crosscheck whether the address in front of the function is also the one we see first afterwards
if not re.match("^0*" + first_addr + "$", first_addr_start):
  print "error during parsing and extracting, exiting."
  sys.exit()


# print some statistics
print ("extracted %d assembly lines." % linecount)
print ("first address is %s." % first_addr)

# remove last character from mlarray string (just a trailing comma)
mlarray = mlarray[:-1]


# write to output file
f = open(outfile, 'w')
f.write("val first_addr = ``0x%sw:word64``;\n\n" % first_addr)
f.write("val last_addr = ``0x%sw:word64``;\n\n" % last_addr)
f.write("val instructions = [\n%s\n];\n" % mlarray)


print "done."
