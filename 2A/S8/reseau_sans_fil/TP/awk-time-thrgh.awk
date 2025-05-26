BEGIN{
 time = 0
 granularity = 0.1
 sum = 0
}

{
 if ($1 - time <= granularity){
     sum = sum + ($2*8)
     temp = $1
  }
  else
  {
     sum = sum + ($2*8)
     printf("%f  %f\n",$1,(sum/($1-time))/1000000)
     time = $1
     sum = 0
 } 
}

