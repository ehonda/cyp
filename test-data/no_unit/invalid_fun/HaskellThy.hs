data TX = X
data TY = Y

f True = X
-- f False = Y
{-
HaskellThy.hs:5:11: error:
    • Couldn't match expected type ‘TX’ with actual type ‘TY’
    • In the expression: Y
      In an equation for ‘f’: f False = Y
  |
5 | f False = Y
  | 
-}

g X = True
-- g Y = False
{-
HaskellThy.hs:17:3: error:
    • Couldn't match expected type ‘TX’ with actual type ‘TY’
    • In the pattern: Y
      In an equation for ‘g’: g Y = False
   |
17 | g Y = False
   |   ^
-}

