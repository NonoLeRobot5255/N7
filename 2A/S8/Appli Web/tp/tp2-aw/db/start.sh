#!/bin/bash

hsqldb_home=./hsqldb
rc_file=auth.rc
urlid=Hagi
sql_file=db.sql

java -cp "$hsqldb_home/lib/hsqldb.jar" org.hsqldb.server.Server --database.0 file:mydb --dbname.0 xdb

