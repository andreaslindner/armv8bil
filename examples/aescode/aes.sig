signature aes =
sig
    include Abbrev

    val first_addr   : term
    val next_addr    : term
    val instructions  : string list
end
