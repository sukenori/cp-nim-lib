import atcoder/string
z_algorithm(s:string) #Z-array i番目の要素はs[i..^1]とs[0..^1]とを左から見ていったときに一致する文字数、最長共通接頭辞の長さ
#SにTが含まれるか確認するなら、T&SのZ-arrayをとって、|T|以上の要素があるか見ればよい