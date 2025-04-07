


fun getPRIVK[name_a:name] : lone Key{
    (KeyPairs.owners).name_a
}
fun getPUBK[name_a:name] : lone Key {
    (KeyPairs.owners.(name_a)).(KeyPairs.pairs)
}
pred learnt_term_by[m:mesg,a:strand,t:Timeslot] {
    m in (a.learned_times).(Timeslot - t.^next)
}

