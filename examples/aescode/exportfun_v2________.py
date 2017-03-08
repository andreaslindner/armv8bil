#!/usr/bin/python

import sys
import re


# read all parameters
if len(sys.argv) <= 3:
  print "too few arguments, exiting."
  print "Usage: exportfun.py dumpfile output.sml output_p.sml"
  sys.exit()


dumpfile   = sys.argv[1]
outfile    = sys.argv[2]
outfile_p  = sys.argv[3]


# read everything from inputfile
with open(dumpfile) as f:
  content = f.readlines()

# extract location and data
def extract_symboldata(dump, symbol):
  # find (the one) matching descriptor
  pattern_descriptor = re.compile("^\s*(?P<start>[0-9a-fA-F]+)[^\.]+(?P<section>\.[^\s]+)\s+(?P<length>0[0-9a-fA-F]+)\s+(?P<symbol>.*)$")
  matched = False
  start   = 0
  length  = 0
  for line in dump:
    m = pattern_descriptor.match(line)
    if m:
      print ("%s" % m.group("symbol") % m.group("section") % m.group("start") % m.group("length"))
      if m.group("symbol").strip() == symbol:
        print ('Found symbol "%s" in section "%s".' % symbol % m.group("section"))
        start   = int(m.group("start"), 16)
        length  = int(m.group("length"), 16)
        assert (start % 4) == 0

        assert not matched
        matched = True

  assert matched

  # extract data in a loop (first find data start, then check consistency of addresses while extracting)
  pattern_data = re.compile("^\s+(?P<start>[0-9a-fA-F]+)\s+(?P<dat0>[0-9a-fA-F]+)\s+(?P<dat1>[0-9a-fA-F]+)\s+(?P<dat2>[0-9a-fA-F]+)\s+(?P<dat3>[0-9a-fA-F]+)\s+................$")
  # last_addr is the state of parsing, first it is -1 until the right line has been found, then it is the last line's address and afterwards it is -2
  last_addr = -1
  sync_addr = (start >> 4) << 4
  data = []
  for line in dump:
    m = pattern_data.match(line)
    if m:
      cur_addr = int(m.group("start"), 16)
      if last_addr == -1:
        # sync
        if cur_addr != sync_addr:
          continue
        last_addr = sync_addr
      elif last_addr == -2:
        # nothing comes again
        assert not (start <= cur_addr && cur_addr < (start + length))
      else:
        # it comes as a block and consecutively
        assert cur_addr == (last_addr + 0x10)
        last_addr = cur_addr

      # calculate how many 4byte words to skip and how many are left, in the current line
      dats_skip = max(0, start - sync_addr) >> 2 # start - sync_addr is always a multiple of 4 here
      dats_left = min(4, (start + length - cur_addr + (4 - 1)) >> 2)
      dats_end  = dats_skip + dats_left

      # are we already done?
      if dats_left == 0:
        last_addr = -2
        continue

      # extend the right number of words
      dat = [m.group("dat0"), m.group("dat1"), m.group("dat2"), m.group("dat3")]
      # using python slicing, i.e., a slice is given by a begin and end index
      data.extend(dat[dats_skip:dats_end])

    else:
      # during parsing within a block, each line is a data line
      assert last_addr == -1 || last_addr == -2

  assert last_addr == -2

  return (start, length, data)

# export given data as sml array (inteded for instruction lifting, so 4byte length and reverse byte order, asserts size and alginment first)
def export_sml_arr(first, size, data):
  return "sml code"

# export given data as hol function (intended for asserting memory contents bytewise)
def export_hol(first, size, data):
  first_addr = 0
  size = 0
  return "hol conjuction"

extract_symboldata(content, "wc_AesEncryptSimplified")


# parse input data
#------------- https://docs.python.org/2/library/re.html
#------------- http://stackoverflow.com/questions/4108561/how-to-exclude-a-character-from-a-regex-group
#------------- >>> r = re.compile(r"[^a-zA-Z0-9-]")
#------------- >>> s = "some#%te_xt&with--##%--5 hy-phens  *#"
#------------- >>> r.sub("",s)
#------------- 'sometextwith----5hy-phens'

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
      addr_val = int(last_addr, 16)
      hol_aesc += '0x%dw => 0x%02Xw\n  | ' % (addr_val + 0) % last_instr[6:8]
      hol_aesc += '0x%dw => 0x%02Xw\n  | ' % (addr_val + 1) % last_instr[4:6]
      hol_aesc += '0x%dw => 0x%02Xw\n  | ' % (addr_val + 2) % last_instr[2:4]
      hol_aesc += '0x%dw => 0x%02Xw\n  | ' % (addr_val + 3) % last_instr[0:2]
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
