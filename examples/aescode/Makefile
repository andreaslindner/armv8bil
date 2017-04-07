main: main.c
	aarch64-linux-gnu-gcc main.c -o main -g3

clean:
	rm -f main dump.asm dump.dat aes.sml aes_p.sml
	/opt/hol_snapshot/bin/Holmake cleanAll

dump.asm: main
	aarch64-linux-gnu-objdump -d main > dump.asm

dump.dat: main
	aarch64-linux-gnu-objdump -s -t main > dump.dat

dump.src: main
	aarch64-linux-gnu-objdump -d -S main 

aes.sml: dump.dat exportscript.py
	./exportscript.py dump.dat aes.sml aes_p.sml

aes_p.sml: aes.sml

to_fix/bil.sml: aes.sml
	cd ..; /opt/hol_snapshot/bin/hol < aescode/test_aes.sml > aescode/to_fix/bil.sml

to_fix/bil_def.sml: aes.sml
	cd ..; /opt/hol_snapshot/bin/hol < aescode/test_aes_def.sml > aescode/to_fix/bil_def.sml

hol: aesCodeScript.sml aesProp1CondScript.sml aes.sml aes_p.sml
	/opt/hol_snapshot/bin/Holmake

aesCodeTheory.sml: hol

aes.bil: aesCodeTheory.sml export_bil.sml
	/opt/hol_snapshot/bin/hol < export_bil.sml
