#!/usr/bin/python

import sys
import re


# read all parameters
if len(sys.argv) <= 3:
  print "too few arguments, exiting."
  print "Usage: exportfun.py dumpfile output_code.sml output_mem.sml"
  sys.exit()


dumpfile   = sys.argv[1]
outfile_c  = sys.argv[2]
outfile_m  = sys.argv[3]


# read everything from inputfile
with open(dumpfile) as f:
  content = f.readlines()

# extract location and data
def extract_symbol(dump, symbol):
  print ('Start looking for symbol descriptor "%s".' % symbol)

  # find (the one) matching descriptor
  pattern_descriptor = re.compile("^\s*(?P<start>[0-9a-fA-F]+)[^\.]+(?P<section>\.[^\s]+)\s+(?P<length>0[0-9a-fA-F]+)\s+(?P<symbol>.*)$")
  matched = False
  start   = 0
  length  = 0
  for line in dump:
    m = pattern_descriptor.match(line)
    if m:
      #print ("symb %s, %s, %s, %s" % (m.group("symbol"), m.group("section"), m.group("start"), m.group("length")))
      if m.group("symbol").strip() == symbol:
        print ('Found symbol "%s" in section "%s".' % (symbol, m.group("section")))
        start   = int(m.group("start"), 16)
        length  = int(m.group("length"), 16)
        print ('"%s" starts at 0x%X, using 0x%X bytes.' % (symbol, start, length))
        assert (start % 4) == 0

        assert not matched
        matched = True

  assert matched
  return (start, length)

def extract_data(dump, (start, length)):
  print "Start fetching data lines."

  if length <= 0:
    return ([], start, length)

  # extract data in a loop (first find data start, then check consistency of addresses while extracting)
  pattern_data = re.compile("^\s+(?P<start>[0-9a-fA-F]+)\s+(?P<dat0>[0-9a-fA-F]+)\s+(((?P<dat1_4>[0-9a-fA-F]+)\s+(?P<dat2_4>[0-9a-fA-F]+)\s+(?P<dat3_4>[0-9a-fA-F]+)\s+................)|((?P<dat1_3>[0-9a-fA-F]+)\s+(?P<dat2_3>[0-9a-fA-F]+)\s+............\s*)|((?P<dat1_2>[0-9a-fA-F]+)\s+........\s*)|(....\s*))$")
  # last_addr is the state of parsing, first it is -1 until the right line has been found, then it is the last line's address and afterwards it is -2
  last_addr = -1
  data = []
  for line in dump:
    m = pattern_data.match(line)
    if m:
      cur_addr = int(m.group("start"), 16)
      numofwordsinthisline = 4 if m.group("dat3_4") else (3 if m.group("dat2_3") else (2 if m.group("dat1_2") else 1))
      if last_addr == -1:
        # sync
        if cur_addr + ((numofwordsinthisline - 1) * 4) < start:
          continue
        last_addr = cur_addr
      elif last_addr == -2:
        # nothing comes again
        assert not (start <= cur_addr and cur_addr < (start + length))
        continue
      else:
        # it comes as a block and consecutively
        assert cur_addr == (last_addr + 0x10)
        last_addr = cur_addr

      bytes_left = length - (len(data) * 4)#wrong: start + length - cur_addr
      #print ("at addr 0x%X, left 0x%X" % (last_addr, bytes_left))

      # calculate how many 4byte words to skip and how many are left, in the current line
      dats_skip = max(0, start - cur_addr) >> 2 # start - sync_addr is always a multiple of 4 here
      dats_left = min(4 - dats_skip, (bytes_left + (4 - 1)) >> 2)
      dats_end  = dats_skip + dats_left
      #print (dats_skip, dats_left, dats_end)

      # are we already done?
      if dats_left <= 0:
        last_addr = -2
        continue

      # build the dat array reflecting the current line
      dat = []
      if m.group("dat3_4"):
        dat = [m.group("dat0"), m.group("dat1_4"), m.group("dat2_4"), m.group("dat3_4")]
      elif m.group("dat2_3"):
        dat = [m.group("dat0"), m.group("dat1_3"), m.group("dat2_3")]
      elif m.group("dat1_2"):
        dat = [m.group("dat0"), m.group("dat1_2")]
      else:
        dat = [m.group("dat0")]
      assert dats_end <= len(dat)

      # extend the right number of 4byte words
      # using python slicing, i.e., a slice is given by a begin and end index
      dat_extend = dat[dats_skip:dats_end]
      data.extend(dat_extend)

      # are we done?
      #print dat_extend
      if (len(dat_extend) * 4) >= bytes_left:
        last_addr = -2

    else:
      # during parsing within a block, each line is a data line
      #print last_addr
      assert last_addr == -1 or last_addr == -2

  assert last_addr == -2
  print ("Finished fetching 0x%X lines." % length)

  return (start, length, data)

def extract_symboldata(dump, symbol):
  (start, length) = extract_symbol(dump, symbol)
  return extract_data(dump, (start, length))

def extract_test():
  print "-------------------------"
  print "START TEST EXTRACT"
  print

  (start, length, data) = extract_symboldata(content, "wc_AesEncryptSimplified")
  assert length == len(data) * 4
  (start, length, data) = extract_symboldata(content, "main")
  assert length == len(data) * 4
  (start, length, data) = extract_symboldata(content, "__libc_csu_init")
  assert length == len(data) * 4
  (start, length, data) = extract_symboldata(content, "__libc_csu_fini")
  assert length == len(data) * 4

  (start, length) = extract_symbol(content, "_init")
  (start, length, data) = extract_data(content, (start, 5*4))
  assert length == len(data) * 4

  (start, length, data) = extract_symboldata(content, "Td4")
  assert length == len(data) * 4

  #print ("0x%X, 0x%X" % (length, len(data) * 4))
  #print data

  print
  print "END TEST EXTRACT"
  print "-------------------------"




# create a byte-sized mapping for the memory area (for easier exporting)
def toByteMap(start, length, data):
  datmap = {}

  # this is not neccessary here: assert length % 4 == 0
  for x in range(0, length):
    addr = start + x
    data_idx = x / 4
    byte_idx = x % 4

    #print ("%d, %d" % (x, length / 4))
    #print ("%s, %d, %d" % (data[x], x, length / 4))
    datmap[addr] = int((data[data_idx])[2*byte_idx : 2*(byte_idx+1)], 16)

  #print datmap
  return datmap





# export given data as sml array (inteded for instruction lifting, so 4byte length and reverse byte order, asserts size and alginment first)
def export_sml_arr(start, length, datmap):
  print "Starting SML array export for instructions."
  mlarray = "[\n  "

  if length <= 0:
    return "[]"

  # make sure we are aligned and have a number of instructions, i.e., length is a multiple of 4
  assert start % 4 == 0
  assert length % 4 == 0

  linecount = 0
  for x in range(0, length / 4):
    linecount += 1
    addr = start + x * 4

    #print ("%X %X %X" % (addr, x, length))

    # append instruction to buffer
    instr = "%02X%02X%02X%02X" % (datmap[addr + 3], datmap[addr + 2], datmap[addr + 1], datmap[addr + 0])
    mlarray += '"%s",' % instr

    # create a nice line length
    if linecount % 7 == 0:
      mlarray += "\n  "

  #print ("%X" % (linecount * 4))

  # remove last character from mlarray string (just a trailing comma)
  mlarray = mlarray[:mlarray.rfind(',') - len(mlarray)] + "\n]"

  print "Finished SML array export for instructions."
  return mlarray

def export_sml_arr_test():
  print "-------------------------"
  print "START TEST EXPORT SML ARR"
  print

  (start, length, data) = extract_symboldata(content, "wc_AesEncryptSimplified")
  #print data
  datmap = toByteMap(start, length, data)

  mlarray = export_sml_arr(start, length, datmap)
  #print mlarray

  print
  print "END TEST EXPORT SML ARR"
  print "-------------------------"




# export given data as hol function (intended for asserting memory contents bytewise)
def export_hol(start, length, datmap):
  print "Starting HOL export as memory function."
  holmemf = "\\(x:word64). case x of\n    "

  linecount = 0
  for x in range(0, length):
    linecount += 1
    addr = start + x

    #print ("%d, %d" % (x, length / 4))
    #print ("%s, %d, %d" % (data[x], x, length / 4))
    holmemf += '0x%Xw:word64 => 0x%02Xw:word8' % (addr, datmap[addr])

    if linecount % 3 == 0:
      holmemf += "\n "
    holmemf += " | "

  holmemf += "_ => 0x0w:word8" # or should we drop this and take ARB value instead?

  print "Finished HOL export as memory function."
  return holmemf

def export_hol_test():
  print "-------------------------"
  print "START TEST EXPORT HOL"
  print

  (start, length, data) = extract_symboldata(content, "Td4")
  #print data
  datmap = toByteMap(start, length, data)

  holmemf = export_hol(start, length, datmap)
  #print holmemf

  print
  print "END TEST EXPORT HOL"
  print "-------------------------"




#extract_test()
#export_sml_arr_test()
#export_hol_test()






def export_hol_2_mk(start, length, datmap):
  print "Starting HOL export as memory function."
  holmemf = ""
#TypeBase.mk_case (``x:word64``, [(``1w:word64``,``5w:word16``), (``3w:word64``,``44w:word16``),(``xx:word64``,``3w:word16``)]);

  linecount = 0
  for x in range(0, length):
    linecount += 1
    addr = start + x

    #print ("%d, %d" % (x, length / 4))
    #print ("%s, %d, %d" % (data[x], x, length / 4))
    holmemf += "(``0x%Xw:word64``,``0x%02Xw:word8``), " % (addr, datmap[addr])#'0x%Xw => 0x%02Xw' % (addr, datmap[addr])

    if linecount % 3 == 0:
      holmemf += "\n  "

  #holmemf += "_ => 0x0w:word8" # or should we drop this and take ARB value instead?
  holmemf = "TypeBase.mk_case (``x:word64``, [\n  %s(``v:word64``,``0w:word8``)\n])" % holmemf

  print "Finished HOL export as memory function."
  return holmemf





def export_hol_3_axiom(start, length, datmap, predprefix):
  print "Starting HOL export as memory function."
  holmemf = ""

  #holmemf += "val %s_memf = ``%s_memf:word64 -> word8``;\n" % (predprefix, predprefix)
  holmemf += 'val _ = new_constant("%s_memf", mk_vartype "word64 -> word8");\n' % predprefix
  holmemf += 'val %s_memf_axiom = new_axiom("%s_memf_axiom", ``\n  ' % (predprefix, predprefix)

  linecount = 0
  for x in range(0, length):
    linecount += 1
    addr = start + x

    #print ("%d, %d" % (x, length / 4))
    #print ("%s, %d, %d" % (data[x], x, length / 4))
    holmemf += "(%s_memf (0x%Xw:word64) = 0x%02Xw:word8) /\\ " % (predprefix, addr, datmap[addr])

    if linecount % 2 == 0:
      holmemf += "\n  "

  #holmemf += "T``);\n"
  holmemf = holmemf[:holmemf.rfind(' /\\') - len(holmemf)] + "\n``);\n"

  print "Finished HOL export as memory function."
  return holmemf


def export_hol_4_list(start, length, datmap, predprefix):
  print "Starting HOL export as memory function."
  hollist = "[\n  "

  linecount = 0
  for x in range(0, length):
    linecount += 1
    addr = start + x

    hollist += "0x%02Xw; " % (datmap[addr])

    if linecount % 12 == 0:
      hollist += "\n  "

  hollist = hollist[:hollist.rfind(';') - len(hollist)] + "\n] : word8 list"

  holmemf = "val %s_meml_def = Define `%s_meml = %s`;\n" % (predprefix, predprefix, hollist)
  holmemf += "val %s_memf_def = Define `(%s_memf (x:word64)):word8 = if x <+ 0x%Xw then 0w else if x >=+ 0x%Xw + 0x%Xw then 0w else EL (w2n (x - 0x%Xw)) %s_meml`;\n" % (predprefix, predprefix, start, start, length, start, predprefix)

  print "Finished HOL export as memory function."
  return holmemf


def export_mem_sml_arr(start, length, datmap):
  print "Starting memory export."
  mlarray = "[\n  "

  if length <= 0:
    return "[]"

  linecount = 0
  for x in range(0, length):
    linecount += 1
    addr = start + x

    mlarray += "``0x%02Xw:word8``," % (datmap[addr])

    if linecount % 12 == 0:
      mlarray += "\n  "

  #print ("%X" % (linecount * 4))

  # remove last character from mlarray string (just a trailing comma)
  mlarray = mlarray[:mlarray.rfind(',') - len(mlarray)] + "\n]"

  print "Finished memory export."
  return mlarray






(start, length, data) = extract_symboldata(content, "wc_AesEncryptSimplified")
datmap = toByteMap(start, length, data)
mlarray = export_sml_arr(start, length, datmap)

# write to output file
f = open(outfile_c, 'w')
f.write("""
structure aes_code :> aes_code =
struct

open HolKernel boolLib bossLib Parse;
open wordsLib;


""")

f.write("val instrs_fstad   = ``0x%Xw:word64``;\n" % start)
f.write("val instrs = %s;\n" % mlarray)


f.write("\nend\n")







def append_sym_predicate(symbol, predprefix):
  (start, length, data) = extract_symboldata(content, symbol)
  #length = 20 #(* this line is just for creating smaller tests for later code *)
  datmap = toByteMap(start, length, data)

  # alternative 1
  #holmemf = export_hol(start, length, datmap)
  #prepstr = ""
  # alternative 2
  #holmemf = export_hol_2_mk(start, length, datmap)
  #prepstr = "val %s_val_case = %s;\n" % (predprefix, holmemf)
  #holmemf = "\\(x:word64). ^%s_val_case" % predprefix
  # alternative 3
  #prepstr = export_hol_3_axiom(start, length, datmap, predprefix)
  #holmemf = "%s_memf:word64->word8" % predprefix
  # alternative 4
  #prepstr = export_hol_4_list(start, length, datmap, predprefix)
  #holmemf = "%s_memf:word64->word8" % predprefix
  mlarray = export_mem_sml_arr(start, length, datmap)
  
  output_content = ""

  #output_content += ("val %s        = ``\\x.((0x%Xw:word64)<=+x)/\\(x<+(0x%Xw:word64))``;\n" % (predprefix, start, start + length))
  #output_content += (prepstr)
  #output_content += ("val %s_val    = ``%s``;\n" % (predprefix, holmemf))
  #output_content += ("val %s_in_mem = ``!addr. ^%s addr ==> (s.MEM addr = ^%s_val addr)``;\n\n\n" % (predprefix, predprefix, predprefix))

  output_content += ("val %s_fstad   = ``0x%Xw:word64``;\n" % (predprefix, start))
  output_content += ("val %s_bytes = %s;\n" % (predprefix, mlarray))

  # write to output_p file, precondition for ARM
  #f.write output_content

  return output_content





f = open(outfile_m, 'w')

#outfile_p_content += ("val aesc_in_mem    = ``^AESC_mem_in_mem``;\n")
#outfile_p_content += ("val prog_counter   = ``s.PC = ^first_addr``;\n")
#outfile_p_content += ("val stack_pointer  = ``s.SP_EL0 = 0x8000000FFw``;\n")
#outfile_p_content += ("val sbox_in_mem    = ``^Te_mem_in_mem /\\ ^Td_mem_in_mem /\\ ^Td4_mem_in_mem``;\n\n\n")

#outfile_p_content += ("val precond_arm = Define `P s = ^aesc_in_mem /\\ ^prog_counter /\\ ^stack_pointer /\\ ^sbox_in_mem`;\n")

f.write("""
structure aes_mem :> aes_mem =
struct

open HolKernel boolLib bossLib Parse;
open wordsLib;


""")

f.write(append_sym_predicate("wc_AesEncryptSimplified", "AESC_mem"))
f.write("\n")
f.write(append_sym_predicate("Te", "Te_mem"))
f.write("\n")
f.write(append_sym_predicate("Td", "Td_mem"))
f.write("\n")
f.write(append_sym_predicate("Td4", "Td4_mem"))
f.write("\n")

f.write("\nend\n")















print "Done."



