assume((y:u32>50:u32) &
       (y:u32 < 0xFFFF:u32))

x:u32 = y:u32 + 10:u32

assert((x:u32 > 5:u32) &
        (y >= 10:u32))
