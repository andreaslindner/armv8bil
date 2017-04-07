signature aes_p =
sig
    include Abbrev

    val first_addr			: term

	val AESC_mem			: term
	val AESC_mem_memf_axiom	: string * term

	val Te_mem				: term
	val Te_mem_memf_axiom	: string * term

	val Td_mem				: term
	val Td_mem_memf_axiom	: string * term

	val Td4_mem				: term
	val Td4_mem_memf_axiom	: string * term

(*    val precond_arm_quot	: term quotation*)
end
