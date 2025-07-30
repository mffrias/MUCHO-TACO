JAVAC    = javac
JAR      = jar
FLAGS    = -source 1.5 -target 1.5
SPATH    = src
BPATH    = bin
CPATH    = bin


cli : $(BPATH)/org/apache/commons/cli $(BPATH)/models
	$(JAVAC) -classpath $(CPATH) \
	         -sourcepath $(SPATH) \
	         -d $(BPATH) \
	            $(FLAGS)  \
	         `find $(SPATH) -name '*.java'`

jar : cli
	@echo 'Main-Class: rfm.alloy.CLI' >.mf.tmp
	$(JAR) -cmf .mf.tmp alloycli-160b2.jar -C $(BPATH)/ .
	rm .mf.tmp

$(BPATH)/models :
	$(JAR) xf assets/models.jar
	mv models/ bin/

$(BPATH)/org/apache/commons/cli :
	mkdir -p $(BPATH)/org/apache/commons/cli
	cp $(SPATH)/org/apache/commons/cli/*.class $(BPATH)/org/apache/commons/cli/
	

clean :
	rm -rf $(BPATH)/* .mf.tmp alloycli-160b2.jar
