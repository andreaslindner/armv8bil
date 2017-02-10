main: main.c
	aarch64-linux-gnu-gcc main.c -o main -g3

clean:
	rm main dump.asm aes.sml bil.sml bil_def.sml

dump.asm: main
	aarch64-linux-gnu-objdump -d main > dump.asm

dump.src: main
	aarch64-linux-gnu-objdump -d -S main 

aes.sml: dump.asm
	./exportfun.py dump.asm wc_AesEncryptSimplified aes.sml

bil.sml: aes.sml
	cd ..; /opt/hol_snapshot/bin/hol < aescode/test_aes.sml > aescode/bil.sml

bil_def.sml: aes.sml
	cd ..; /opt/hol_snapshot/bin/hol < aescode/test_aes_def.sml > aescode/bil_def.sml



