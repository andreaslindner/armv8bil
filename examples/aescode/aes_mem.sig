signature aes_mem =
sig
    include Abbrev


    val AESC_mem_fstad	: term
    val AESC_mem_bytes	: term list

    val Te_mem_fstad	: term
    val Te_mem_bytes	: term list

    val Td_mem_fstad	: term
    val Td_mem_bytes	: term list

    val Td4_mem_fstad	: term
    val Td4_mem_bytes	: term list

end
