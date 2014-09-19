module Banana where
 
data Banana : Set where
  cons : Banana -> Banana
  nil : Banana

a : Banana
a = cons nil

b : Banana
b = {!nil!}

