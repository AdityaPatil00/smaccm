
############################################################################
#
#   File: /home/ajgacek/smaccm/models/Trusted_Build_Test/camera_vm/make_template/Makefile
#   Created on: 2015/06/10 10:30:46
#   using Dulcimer AADL system build tool suite 
#
#   ***AUTOGENERATED CODE (modify if you need to :-) ***
#
# TODO: add DARPA license?
#
# This file is an automatically generated makefile from the AADL build 
# system designed for the CAmkES build system.  It will work for projects 
# in which all C files and libraries are "known" to the AADL file.  
# However, for projects with more complex dependencies and "external" 
# components that are not described in the AADL file, it will need to be 
# extended.
#
############################################################################
TARGETS := $(notdir ${SOURCE_DIR}).cdl
ADL := wrapper_i_assembly.camkes

# For time server: subdirectory containing extra templates.
TEMPLATES := ../../projects/templates ../../projects/global-components/templates


include TimeServerOdroid/TimeServer.mk
camera_vm_CFILES :=  \
    $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/camera_vm/src/*.c)) \
    $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/camera_vm/src/plat/${PLAT}/*.c)) \
    $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/camera_vm/src/arch/${ARCH}/*.c))

camera_vm_HFILES := \
   $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/camera_vm/include/*.h)) \
   $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/include/*.h))

camera_vm_ASMFILES := \
    $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/camera_vm/crt/arch-${ARCH}/crt0.S)) \
    $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/camera_vm/src/*.S)) \
    $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/camera_vm/src/arch/${ARCH}/*.S)) \
    $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/camera_vm/src/plat/${PLAT}/*.S))

receiver_CFILES :=  \
    $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/receiver/src/*.c)) \
    $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/receiver/src/plat/${PLAT}/*.c)) \
    $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/receiver/src/arch/${ARCH}/*.c))

receiver_HFILES := \
   $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/receiver/include/*.h)) \
   $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/include/*.h))

receiver_ASMFILES := \
    $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/receiver/crt/arch-${ARCH}/crt0.S)) \
    $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/receiver/src/*.S)) \
    $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/receiver/src/arch/${ARCH}/*.S)) \
    $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/receiver/src/plat/${PLAT}/*.S))


include ${PWD}/tools/camkes/camkes.mk
###################################################################
#
# End of autogenerated file: unused
#
###################################################################

