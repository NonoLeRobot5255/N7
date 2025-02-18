#!/bin/bash

hsqldb_home=./hsqldb
rc_file=auth.rc
urlid=Hagi
sql_file=db.sql

java -cp "$hsqldb_home/lib/sqltool.jar" org.hsqldb.util.DatabaseManagerSwing --rcFile $rc_file --urlid $urlid 

