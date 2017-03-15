main: main.c
	aarch64-linux-gnu-gcc main.c -o main -g3

clean:
	rm main dump.asm dump.dat aes.sml aes_p.sml bil.sml bil_def.sml
	/opt/hol_snapshot/bin/Holmake cleanAll

dump.asm: main
	aarch64-linux-gnu-objdump -d main > dump.asm

dump.dat: main
	aarch64-linux-gnu-objdump -s -t main > dump.dat

dump.src: main
	aarch64-linux-gnu-objdump -d -S main 

aes.sml: dump.dat
	./exportscript.py dump.dat aes.sml aes_p.sml

aes_p.sml: aes.sml

bil.sml: aes.sml
	cd ..; /opt/hol_snapshot/bin/hol < aescode/test_aes.sml > aescode/bil.sml

bil_def.sml: aes.sml
	cd ..; /opt/hol_snapshot/bin/hol < aescode/test_aes_def.sml > aescode/bil_def.sml

aesCodeTheory.sml: aesCodeScript.sml aes.sml
	/opt/hol_snapshot/bin/Holmake aesCodeTheory.sml
	/opt/hol_snapshot/bin/Holmake aesCodeTheory.ui
	/opt/hol_snapshot/bin/Holmake aesCodeTheory.uo

