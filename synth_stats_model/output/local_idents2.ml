let counts =
  [ ("NthInEnv 0", 24644)
  ; ("NthInEnv 1", 15572)
  ; ("NthInEnv 2", 9133)
  ; ("NthInEnv 3", 5660)
  ; ("NthInEnv 4", 4093)
  ; ("NthInEnv 5", 2573)
  ; ("NthInEnv 6", 2009)
  ; ("NthInEnv 7", 1338)
  ; ("NthInEnv 8", 1288)
  ; ("NthInEnv 11", 1165)
  ; ("NthInEnv 9", 1086)
  ; ("NthInEnv 12", 742)
  ; ("NthInEnv 10", 675)
  ; ("NthInEnv 15", 580)
  ; ("NthInEnv 13", 392)
  ; ("NthInEnv 16", 374)
  ; ("NthInEnv 53", 364)
  ; ("NthInEnv 54", 309)
  ; ("NthInEnv 52", 285)
  ; ("NthInEnv 26", 269)
  ; ("NthInEnv 29", 257)
  ; ("NthInEnv 14", 248)
  ; ("NthInEnv 18", 244)
  ; ("NthInEnv 28", 215)
  ; ("NthInEnv 27", 209)
  ; ("NthInEnv 21", 195)
  ; ("NthInEnv 19", 179)
  ; ("NthInEnv 23", 177)
  ; ("NthInEnv 17", 176)
  ; ("NthInEnv 48", 175)
  ; ("NthInEnv 38", 155)
  ; ("NthInEnv 31", 152)
  ; ("NthInEnv 51", 150)
  ; ("NthInEnv 20", 150)
  ; ("NthInEnv 30", 144)
  ; ("NthInEnv 43", 138)
  ; ("NthInEnv 25", 138)
  ; ("NthInEnv 22", 136)
  ; ("NthInEnv 41", 135)
  ; ("NthInEnv 47", 129)
  ; ("NthInEnv 24", 129)
  ; ("NthInEnv 44", 127)
  ; ("NthInEnv 33", 124)
  ; ("NthInEnv 36", 121)
  ; ("NthInEnv 64", 117)
  ; ("NthInEnv 63", 115)
  ; ("NthInEnv 49", 109)
  ; ("NthInEnv 46", 102)
  ; ("NthInEnv 35", 99)
  ; ("NthInEnv 50", 94)
  ; ("NthInEnv 34", 91)
  ; ("NthInEnv 39", 86)
  ; ("NthInEnv 45", 79)
  ; ("NthInEnv 37", 75)
  ; ("NthInEnv 59", 60)
  ; ("NthInEnv 32", 56)
  ; ("NthInEnv 55", 54)
  ; ("NthInEnv 40", 54)
  ; ("NthInEnv 66", 52)
  ; ("NthInEnv 61", 50)
  ; ("NthInEnv 42", 49)
  ; ("NthInEnv 62", 48)
  ; ("NthInEnv 96", 47)
  ; ("NthInEnv 86", 46)
  ; ("NthInEnv 95", 43)
  ; ("NthInEnv 85", 42)
  ; ("NthInEnv 60", 42)
  ; ("NthInEnv 97", 35)
  ; ("NthInEnv 94", 35)
  ; ("NthInEnv 58", 31)
  ; ("NthInEnv 87", 30)
  ; ("NthInEnv 65", 29)
  ; ("NthInEnv 90", 28)
  ; ("NthInEnv 75", 28)
  ; ("NthInEnv 89", 27)
  ; ("NthInEnv 93", 26)
  ; ("NthInEnv 98", 25)
  ; ("NthInEnv 88", 25)
  ; ("NthInEnv 56", 25)
  ; ("NthInEnv 73", 24)
  ; ("NthInEnv 72", 23)
  ; ("NthInEnv 70", 23)
  ; ("NthInEnv 57", 23)
  ; ("NthInEnv 68", 22)
  ; ("NthInEnv 67", 22)
  ; ("NthInEnv 84", 21)
  ; ("NthInEnv 81", 21)
  ; ("NthInEnv 71", 21)
  ; ("NthInEnv 119", 21)
  ; ("NthInEnv 91", 20)
  ; ("NthInEnv 76", 20)
  ; ("NthInEnv 69", 20)
  ; ("NthInEnv 99", 19)
  ; ("NthInEnv 83", 17)
  ; ("NthInEnv 80", 17)
  ; ("NthInEnv 74", 16)
  ; ("NthInEnv 92", 15)
  ; ("NthInEnv 82", 15)
  ; ("NthInEnv 109", 15)
  ; ("NthInEnv 105", 14)
  ; ("NthInEnv 103", 14)
  ; ("NthInEnv 106", 13)
  ; ("NthInEnv 102", 13)
  ; ("NthInEnv 115", 12)
  ; ("NthInEnv 118", 11)
  ; ("NthInEnv 101", 11)
  ; ("NthInEnv 100", 11)
  ; ("NthInEnv 77", 10)
  ; ("NthInEnv 130", 10)
  ; ("NthInEnv 114", 10)
  ; ("NthInEnv 79", 9)
  ; ("NthInEnv 78", 9)
  ; ("NthInEnv 138", 9)
  ; ("NthInEnv 137", 9)
  ; ("NthInEnv 213", 8)
  ; ("NthInEnv 129", 8)
  ; ("NthInEnv 124", 8)
  ; ("NthInEnv 108", 8)
  ; ("NthInEnv 104", 8)
  ; ("NthInEnv 189", 7)
  ; ("NthInEnv 183", 7)
  ; ("NthInEnv 131", 7)
  ; ("NthInEnv 127", 7)
  ; ("NthInEnv 120", 7)
  ; ("NthInEnv 117", 7)
  ; ("NthInEnv 107", 7)
  ; ("NthInEnv 200", 6)
  ; ("NthInEnv 192", 6)
  ; ("NthInEnv 185", 6)
  ; ("NthInEnv 177", 6)
  ; ("NthInEnv 154", 6)
  ; ("NthInEnv 152", 6)
  ; ("NthInEnv 135", 6)
  ; ("NthInEnv 128", 6)
  ; ("NthInEnv 125", 6)
  ; ("NthInEnv 123", 6)
  ; ("NthInEnv 121", 6)
  ; ("NthInEnv 116", 6)
  ; ("NthInEnv 111", 6)
  ; ("NthInEnv 110", 6)
  ; ("NthInEnv 242", 5)
  ; ("NthInEnv 226", 5)
  ; ("NthInEnv 214", 5)
  ; ("NthInEnv 207", 5)
  ; ("NthInEnv 194", 5)
  ; ("NthInEnv 173", 5)
  ; ("NthInEnv 172", 5)
  ; ("NthInEnv 157", 5)
  ; ("NthInEnv 140", 5)
  ; ("NthInEnv 136", 5)
  ; ("NthInEnv 134", 5)
  ; ("NthInEnv 133", 5)
  ; ("NthInEnv 132", 5)
  ; ("NthInEnv 126", 5)
  ; ("NthInEnv 122", 5)
  ; ("NthInEnv 113", 5)
  ; ("NthInEnv 112", 5)
  ; ("NthInEnv 239", 4)
  ; ("NthInEnv 232", 4)
  ; ("NthInEnv 230", 4)
  ; ("NthInEnv 225", 4)
  ; ("NthInEnv 219", 4)
  ; ("NthInEnv 218", 4)
  ; ("NthInEnv 212", 4)
  ; ("NthInEnv 211", 4)
  ; ("NthInEnv 206", 4)
  ; ("NthInEnv 205", 4)
  ; ("NthInEnv 204", 4)
  ; ("NthInEnv 196", 4)
  ; ("NthInEnv 193", 4)
  ; ("NthInEnv 178", 4)
  ; ("NthInEnv 176", 4)
  ; ("NthInEnv 175", 4)
  ; ("NthInEnv 174", 4)
  ; ("NthInEnv 171", 4)
  ; ("NthInEnv 169", 4)
  ; ("NthInEnv 158", 4)
  ; ("NthInEnv 155", 4)
  ; ("NthInEnv 153", 4)
  ; ("NthInEnv 151", 4)
  ; ("NthInEnv 149", 4)
  ; ("NthInEnv 148", 4)
  ; ("NthInEnv 144", 4)
  ; ("NthInEnv 203", 3)
  ; ("NthInEnv 199", 3)
  ; ("NthInEnv 195", 3)
  ; ("NthInEnv 191", 3)
  ; ("NthInEnv 190", 3)
  ; ("NthInEnv 186", 3)
  ; ("NthInEnv 184", 3)
  ; ("NthInEnv 164", 3)
  ; ("NthInEnv 162", 3)
  ; ("NthInEnv 159", 3)
  ; ("NthInEnv 156", 3)
  ; ("NthInEnv 150", 3)
  ; ("NthInEnv 146", 3)
  ; ("NthInEnv 145", 3)
  ; ("NthInEnv 143", 3)
  ; ("NthInEnv 141", 3)
  ; ("NthInEnv 139", 3)
  ; ("NthInEnv 370", 2)
  ; ("NthInEnv 351", 2)
  ; ("NthInEnv 245", 2)
  ; ("NthInEnv 241", 2)
  ; ("NthInEnv 227", 2)
  ; ("NthInEnv 222", 2)
  ; ("NthInEnv 221", 2)
  ; ("NthInEnv 220", 2)
  ; ("NthInEnv 209", 2)
  ; ("NthInEnv 208", 2)
  ; ("NthInEnv 202", 2)
  ; ("NthInEnv 198", 2)
  ; ("NthInEnv 188", 2)
  ; ("NthInEnv 181", 2)
  ; ("NthInEnv 179", 2)
  ; ("NthInEnv 168", 2)
  ; ("NthInEnv 167", 2)
  ; ("NthInEnv 166", 2)
  ; ("NthInEnv 160", 2)
  ; ("NthInEnv 428", 1)
  ; ("NthInEnv 424", 1)
  ; ("NthInEnv 396", 1)
  ; ("NthInEnv 365", 1)
  ; ("NthInEnv 357", 1)
  ; ("NthInEnv 353", 1)
  ; ("NthInEnv 350", 1)
  ; ("NthInEnv 274", 1)
  ; ("NthInEnv 262", 1)
  ; ("NthInEnv 256", 1)
  ; ("NthInEnv 255", 1)
  ; ("NthInEnv 254", 1)
  ; ("NthInEnv 249", 1)
  ; ("NthInEnv 247", 1)
  ; ("NthInEnv 243", 1)
  ; ("NthInEnv 240", 1)
  ; ("NthInEnv 229", 1)
  ; ("NthInEnv 228", 1)
  ; ("NthInEnv 224", 1)
  ; ("NthInEnv 223", 1)
  ; ("NthInEnv 217", 1)
  ; ("NthInEnv 216", 1)
  ; ("NthInEnv 215", 1)
  ; ("NthInEnv 210", 1)
  ; ("NthInEnv 201", 1)
  ; ("NthInEnv 197", 1)
  ; ("NthInEnv 187", 1)
  ; ("NthInEnv 182", 1)
  ; ("NthInEnv 180", 1)
  ; ("NthInEnv 170", 1)
  ; ("NthInEnv 165", 1)
  ; ("NthInEnv 163", 1)
  ; ("NthInEnv 161", 1)
  ; ("NthInEnv 147", 1)
  ]