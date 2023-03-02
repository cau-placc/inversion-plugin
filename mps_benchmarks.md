
06:48:05 ~/Projects/inversion-plugin {lifting_changes} $ time stack exec main -- +RTS -N1
Number of cores available: 24
Number of threads used: 1
Pos (S (S (S (S I))))

real	1m32,922s
user	1m32,318s
sys	0m0,357s
06:49:40 ~/Projects/inversion-plugin {lifting_changes} $ time stack exec main -- +RTS -N2
Number of cores available: 24
Number of threads used: 2
Pos (S (S (S (S I))))

real	0m52,124s
user	1m41,190s
sys	0m1,814s
06:50:43 ~/Projects/inversion-plugin {lifting_changes} $ time stack exec main -- +RTS -N3
Number of cores available: 24
Number of threads used: 3
Pos (S (S (S (S I))))

real	0m34,945s
user	1m21,966s
sys	0m3,090s
06:51:31 ~/Projects/inversion-plugin {lifting_changes} $ time stack exec main -- +RTS -N4
Number of cores available: 24
Number of threads used: 4
Pos (S (S (S (S I))))

real	0m27,493s
user	1m43,171s
sys	0m3,219s
06:52:05 ~/Projects/inversion-plugin {lifting_changes} $ time stack exec main -- +RTS -N5
Number of cores available: 24
Number of threads used: 5
Pos (S (S (S (S I))))

real	0m22,781s
user	1m46,261s
sys	0m3,268s
06:52:35 ~/Projects/inversion-plugin {lifting_changes} $ time stack exec main -- +RTS -N6
Number of cores available: 24
Number of threads used: 6
Pos (S (S (S (S I))))

real	0m19,344s
user	1m27,390s
sys	0m5,024s
06:52:59 ~/Projects/inversion-plugin {lifting_changes} $ time stack exec main -- +RTS -N7
Number of cores available: 24
Number of threads used: 7
^C
real	1m19,940s
user	3m2,994s
sys	0m21,953s

06:54:23 ~/Projects/inversion-plugin {lifting_changes} $ time stack exec main -- +RTS -N7
Number of cores available: 24
Number of threads used: 7
^C

real	0m42,999s
user	2m10,859s
sys	0m14,011s
06:55:08 ~/Projects/inversion-plugin {lifting_changes} $ time stack exec main -- +RTS -N8
Number of cores available: 24
Number of threads used: 8
Pos (S (S (S (S I))))

real	0m18,013s
user	1m18,684s
sys	0m8,426s
06:55:28 ~/Projects/inversion-plugin {lifting_changes} $ time stack exec main -- +RTS -N12
Number of cores available: 24
Number of threads used: 12
Pos (S (S (S (S I))))

real	0m11,843s
user	1m40,757s
sys	0m9,158s
06:55:47 ~/Projects/inversion-plugin {lifting_changes} $ time stack exec main -- +RTS -N24
Number of cores available: 24
Number of threads used: 24
Pos (S (S (S (S I))))

real	0m9,568s
user	1m52,622s
sys	0m23,104s
06:56:05 ~/Projects/inversion-plugin {lifting_changes} $
07:21:20 ~/Projects/inversion-plugin {lifting_changes} $ time stack exec main -- +RTS -N2
Number of cores available: 24
Number of threads used: 2
Pos (S (S (S (S I))))

real	0m51,915s
user	1m40,797s
sys	0m1,793s
07:22:19 ~/Projects/inversion-plugin {lifting_changes} $ time stack exec main -- +RTS -N4
Number of cores available: 24
Number of threads used: 4
Pos (S (S (S (S I))))

real	0m27,281s
user	1m43,304s
sys	0m2,746s
07:22:55 ~/Projects/inversion-plugin {lifting_changes} $ time stack exec main -- +RTS -N8
Number of cores available: 24
Number of threads used: 8
Pos (S (S (S (S I))))

real	0m17,720s
user	1m12,923s
sys	0m7,298s
07:23:27 ~/Projects/inversion-plugin {lifting_changes} $ time stack exec main -- +RTS -N16
Number of cores available: 24
Number of threads used: 16
Pos (S (S (S (S I))))

real	0m10,856s
user	1m3,319s
sys	0m15,203s
