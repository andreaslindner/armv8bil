main: main.c
	aarch64-linux-gnu-gcc main.c -o main -g3

clean:
	rm -f main dump.asm dump.dat aes_code.sml aes_mem.sml
	/opt/hol_snapshot/bin/Holmake cleanAll

dump.asm: main
	aarch64-linux-gnu-objdump -d main > dump.asm

dump.dat: main
	aarch64-linux-gnu-objdump -s -t main > dump.dat

dump.src: main
	aarch64-linux-gnu-objdump -d -S main 


aes_mem.sml: aes_code.sml
aes_code.sml: dump.dat exportscript.py
	./exportscript.py dump.dat aes_code.sml aes_mem.sml

#to_fix/bil.sml: aes.sml
#	cd ..; /opt/hol_snapshot/bin/hol < aescode/test_aes.sml > aescode/to_fix/bil.sml
#
#to_fix/bil_def.sml: aes.sml
#	cd ..; /opt/hol_snapshot/bin/hol < aescode/test_aes_def.sml > aescode/to_fix/bil_def.sml


aesCodeTheory.sml: hol
aesProp1CondTheory.sml: hol
hol: aesCodeScript.sml aesProp1CondScript.sml aes_code.sml aes_mem.sml
	/opt/hol_snapshot/bin/Holmake


aes.bil: aesCodeTheory.sml export_bil.sml
	/opt/hol_snapshot/bin/hol < export_bil.sml
