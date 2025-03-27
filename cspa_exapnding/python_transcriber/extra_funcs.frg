


fun getPRIVK[name_a:name] : lone Key{
    (KeyPairs.owners).name_a
}
fun getPUBK[name_a:name] : lone Key {
    (KeyPairs.owners.(name_a)).(KeyPairs.pairs)
}


