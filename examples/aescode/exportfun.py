#!/usr/bin/python

import sys
import re


# read all parameters
if len(sys.argv) < (3 + 1):
  print "too few arguments, exiting."
  print "Usage: exportfun.py dumpfile funname output.sml output_p.sml"
  sys.exit()


dumpfile   = sys.argv[1]
funname    = sys.argv[2]
outfile    = sys.argv[3]
outfile_p  = sys.argv[4]


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
hol_aesc = "\\(x:word64). case x of\n    "
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
      last_instr = m.group("instr")

      # write instruction array
      mlarray += '"%s",' % last_instr

      # watch out! reverse byte order!
      addr_val = int(last_addr)
      hol_aesc += '0x%dw => 0x%02Xw\n  | ' % (addr_val + 0) % last_instr[14:16]
      hol_aesc += '0x%dw => 0x%02Xw\n  | ' % (addr_val + 1) % last_instr[12:14]
      hol_aesc += '0x%dw => 0x%02Xw\n  | ' % (addr_val + 2) % last_instr[10:12]
      hol_aesc += '0x%dw => 0x%02Xw\n  | ' % (addr_val + 3) % last_instr[8:10]
      hol_aesc += '0x%dw => 0x%02Xw\n  | ' % (addr_val + 4) % last_instr[6:8]
      hol_aesc += '0x%dw => 0x%02Xw\n  | ' % (addr_val + 5) % last_instr[4:6]
      hol_aesc += '0x%dw => 0x%02Xw\n  | ' % (addr_val + 6) % last_instr[2:4]
      hol_aesc += '0x%dw => 0x%02Xw\n  | ' % (addr_val + 7) % last_instr[0:2]
      if linecount % 7 == 0:
        mlarray += "\n"
    elif not line.strip():
      continue
    else:
      print "cannot parse the following line, exiting."
      print line
      sys.exit()


hol_aesc += "_ => 0x0w:word8" # or should we drop this and take ARB value instead?


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
f.write("val first_addr   = ``0x%sw:word64``;\n" % first_addr)
f.write("val last_addr    = ``0x%sw:word64``;\n\n" % last_addr)

f.write("val instructions = [\n%s\n];\n" % mlarray)




# write to output_p file, precondition for ARM
f = open(outfile_p, 'w')
f.write("val first_addr     = ``0x%sw:word64``;\n" % first_addr)
f.write("val last_addr      = ``0x%sw:word64``;\n" % last_addr)
f.write("val AESC_mem       = ``\\x.((^first_addr)<=+x)/\\(x<+(^last_addr))``;\n")
f.write("val AESC_mem_val   = ``%s``;\n\n\n" % hol_aesc)

#Te
#Td
#Td4

f.write("val aesc_in_mem    = ``!addr. ^AESC_mem addr ==> (a.MEM addr = ^AESC_mem_val addr)``;\n")
f.write("val prog_counter   = ``a.PC = ^first_addr``;\n")
f.write("val stack_pointer  = ``a.SP_EL0 = 0x8000000FFw``;\n")
f.write("val sbox_in_mem    = ``T``;\n\n\n")

f.write("val precond_arm = Define `P a = ^aesc_in_mem /\\ ^prog_counter /\\ ^stack_pointer /\\ ^sbox_in_mem`;\n")






print "done."
