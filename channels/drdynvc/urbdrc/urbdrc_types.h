/**
 * FreeRDP: A Remote Desktop Protocol client.
 * RemoteFX USB Redirection
 *
 * Copyright 2012 Atrust corp.
 * Copyright 2012 Alfred Liu <alfred.liu@atruscorp.com>
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */



#ifndef __URBDRC_TYPES_H
#define __URBDRC_TYPES_H


#include "config.h"
#include <freerdp/dvc.h>
#include <freerdp/types.h>
#include <freerdp/utils/debug.h>
#include <freerdp/utils/stream.h>
#include <freerdp/utils/msusb.h>
#include "drdynvc_types.h"

#include <uuid/uuid.h>
#include <pthread.h>
#include <semaphore.h>

#define CAPABILITIES_NEGOTIATOR             0x00000000
#define CLIENT_DEVICE_SINK                  0x00000001
#define SERVER_CHANNEL_NOTIFICATION         0x00000002
#define CLIENT_CHANNEL_NOTIFICATION         0x00000003
#define BASE_USBDEVICE_NUM                  0x00000005

#define RIMCALL_RELEASE                     0x00000001
#define RIM_EXCHANGE_CAPABILITY_REQUEST     0x00000100
#define CHANNEL_CREATED                     0x00000100
#define ADD_VIRTUAL_CHANNEL                 0x00000100
#define ADD_DEVICE                          0x00000101


#define INIT_CHANNEL_IN     1
#define INIT_CHANNEL_OUT    0


/* InterfaceClass */
#define CLASS_RESERVE                   0x00
#define CLASS_AUDIO                     0x01
#define CLASS_COMMUNICATION_IF          0x02
#define CLASS_HID                       0x03
#define CLASS_PHYSICAL                  0x05
#define CLASS_IMAGE                     0x06
#define CLASS_PRINTER                   0x07
#define CLASS_MASS_STORAGE              0x08
#define CLASS_HUB                       0x09
#define CLASS_COMMUNICATION_DATA_IF     0x0a
#define CLASS_SMART_CARD                0x0b
#define CLASS_CONTENT_SECURITY          0x0d
#define CLASS_VIDEO                     0x0e
#define CLASS_PERSONAL_HEALTHCARE       0x0f
#define CLASS_DIAGNOSTIC                0xdc
#define CLASS_WIRELESS_CONTROLLER       0xe0
#define CLASS_ELSE_DEVICE               0xef
#define CLASS_DEPENDENCE                0xfe
#define CLASS_VENDOR_DEPENDENCE         0xff


/* usb version */
#define USB_v1_0  0x100
#define USB_v1_1  0x110
#define USB_v2_0  0x200
#define USB_v3_0  0x300

#define STREAM_ID_NONE  0x0
#define STREAM_ID_PROXY 0x1
#define STREAM_ID_STUB  0x2

#define CANCEL_REQUEST             0x00000100
#define REGISTER_REQUEST_CALLBACK  0x00000101
#define IO_CONTROL                 0x00000102
#define INTERNAL_IO_CONTROL        0x00000103
#define QUERY_DEVICE_TEXT          0x00000104
#define TRANSFER_IN_REQUEST        0x00000105
#define TRANSFER_OUT_REQUEST       0x00000106
#define RETRACT_DEVICE             0x00000107


#define IOCONTROL_COMPLETION       0x00000100
#define URB_COMPLETION             0x00000101
#define URB_COMPLETION_NO_DATA     0x00000102

/* The USB device is to be stopped from being redirected because the
 * device is blocked by the server's policy. */
#define UsbRetractReason_BlockedByPolicy  0x00000001



enum device_text_type {
	DeviceTextDescription = 0, 
	DeviceTextLocationInformation = 1,
};

enum device_descriptor_table {
	B_LENGTH = 0, 
	B_DESCRIPTOR_TYPE = 1, 
	BCD_USB = 2, 
	B_DEVICE_CLASS = 4,
	B_DEVICE_SUBCLASS = 5, 
	B_DEVICE_PROTOCOL = 6,
	B_MAX_PACKET_SIZE0 = 7, 
	ID_VENDOR = 8, 
	ID_PRODUCT = 10,
	BCD_DEVICE = 12, 
	I_MANUFACTURER = 14,
	I_PRODUCT = 15, 
	I_SERIAL_NUMBER = 16, 
	B_NUM_CONFIGURATIONS = 17
};


#define PIPE_CANCEL     0
#define PIPE_RESET      1

#define IOCTL_INTERNAL_USB_SUBMIT_URB               0x00220003
#define IOCTL_INTERNAL_USB_RESET_PORT               0x00220007
#define IOCTL_INTERNAL_USB_GET_PORT_STATUS          0x00220013
#define IOCTL_INTERNAL_USB_CYCLE_PORT               0x0022001F
#define IOCTL_INTERNAL_USB_SUBMIT_IDLE_NOTIFICATION 0x00220027



#define URB_FUNCTION_SELECT_CONFIGURATION            0x0000
#define URB_FUNCTION_SELECT_INTERFACE                0x0001
#define URB_FUNCTION_ABORT_PIPE                      0x0002
#define URB_FUNCTION_TAKE_FRAME_LENGTH_CONTROL       0x0003
#define URB_FUNCTION_RELEASE_FRAME_LENGTH_CONTROL    0x0004
#define URB_FUNCTION_GET_FRAME_LENGTH                0x0005
#define URB_FUNCTION_SET_FRAME_LENGTH                0x0006
#define URB_FUNCTION_GET_CURRENT_FRAME_NUMBER        0x0007
#define URB_FUNCTION_CONTROL_TRANSFER                0x0008
#define URB_FUNCTION_BULK_OR_INTERRUPT_TRANSFER      0x0009
#define URB_FUNCTION_ISOCH_TRANSFER                  0x000A
#define URB_FUNCTION_GET_DESCRIPTOR_FROM_DEVICE      0x000B
#define URB_FUNCTION_SET_DESCRIPTOR_TO_DEVICE        0x000C
#define URB_FUNCTION_SET_FEATURE_TO_DEVICE           0x000D
#define URB_FUNCTION_SET_FEATURE_TO_INTERFACE        0x000E
#define URB_FUNCTION_SET_FEATURE_TO_ENDPOINT         0x000F
#define URB_FUNCTION_CLEAR_FEATURE_TO_DEVICE         0x0010
#define URB_FUNCTION_CLEAR_FEATURE_TO_INTERFACE      0x0011
#define URB_FUNCTION_CLEAR_FEATURE_TO_ENDPOINT       0x0012
#define URB_FUNCTION_GET_STATUS_FROM_DEVICE          0x0013
#define URB_FUNCTION_GET_STATUS_FROM_INTERFACE       0x0014
#define URB_FUNCTION_GET_STATUS_FROM_ENDPOINT        0x0015
#define URB_FUNCTION_RESERVED_0X0016                 0x0016
#define URB_FUNCTION_VENDOR_DEVICE                   0x0017
#define URB_FUNCTION_VENDOR_INTERFACE                0x0018
#define URB_FUNCTION_VENDOR_ENDPOINT                 0x0019
#define URB_FUNCTION_CLASS_DEVICE                    0x001A
#define URB_FUNCTION_CLASS_INTERFACE                 0x001B
#define URB_FUNCTION_CLASS_ENDPOINT                  0x001C
#define URB_FUNCTION_RESERVE_0X001D                  0x001D
#define URB_FUNCTION_SYNC_RESET_PIPE_AND_CLEAR_STALL 0x001E
#define URB_FUNCTION_CLASS_OTHER                     0x001F
#define URB_FUNCTION_VENDOR_OTHER                    0x0020
#define URB_FUNCTION_GET_STATUS_FROM_OTHER           0x0021
#define URB_FUNCTION_CLEAR_FEATURE_TO_OTHER          0x0022
#define URB_FUNCTION_SET_FEATURE_TO_OTHER            0x0023
#define URB_FUNCTION_GET_DESCRIPTOR_FROM_ENDPOINT    0x0024
#define URB_FUNCTION_SET_DESCRIPTOR_TO_ENDPOINT      0x0025
#define URB_FUNCTION_GET_CONFIGURATION               0x0026
#define URB_FUNCTION_GET_INTERFACE                   0x0027
#define URB_FUNCTION_GET_DESCRIPTOR_FROM_INTERFACE   0x0028
#define URB_FUNCTION_SET_DESCRIPTOR_TO_INTERFACE     0x0029
#define URB_FUNCTION_GET_MS_FEATURE_DESCRIPTOR       0x002A
#define URB_FUNCTION_RESERVE_0X002B                  0x002B
#define URB_FUNCTION_RESERVE_0X002C                  0x002C
#define URB_FUNCTION_RESERVE_0X002D                  0x002D
#define URB_FUNCTION_RESERVE_0X002E                  0x002E
#define URB_FUNCTION_RESERVE_0X002F                  0x002F
// USB 2.0 calls start at 0x0030
#define URB_FUNCTION_SYNC_RESET_PIPE                 0x0030
#define URB_FUNCTION_SYNC_CLEAR_STALL                0x0031
#define URB_FUNCTION_CONTROL_TRANSFER_EX             0x0032




#define USBD_STATUS_SUCCESS                 0x0
#define USBD_STATUS_PENDING                 0x40000000
#define USBD_STATUS_CANCELED                0xC0010000

#define USBD_STATUS_CRC                     0xC0000001
#define USBD_STATUS_BTSTUFF                 0xC0000002
#define USBD_STATUS_DATA_TOGGLE_MISMATCH    0xC0000003
#define USBD_STATUS_STALL_PID               0xC0000004
#define USBD_STATUS_DEV_NOT_RESPONDING      0xC0000005
#define USBD_STATUS_PID_CHECK_FAILURE       0xC0000006
#define USBD_STATUS_UNEXPECTED_PID          0xC0000007
#define USBD_STATUS_DATA_OVERRUN            0xC0000008
#define USBD_STATUS_DATA_UNDERRUN           0xC0000009
#define USBD_STATUS_RESERVED1               0xC000000A
#define USBD_STATUS_RESERVED2               0xC000000B
#define USBD_STATUS_BUFFER_OVERRUN          0xC000000C
#define USBD_STATUS_BUFFER_UNDERRUN         0xC000000D

/* unknow */
#define USBD_STATUS_NO_DATA                 0xC000000E

#define USBD_STATUS_NOT_ACCESSED            0xC000000F
#define USBD_STATUS_FIFO                    0xC0000010
#define USBD_STATUS_XACT_ERROR              0xC0000011
#define USBD_STATUS_BABBLE_DETECTED         0xC0000012
#define USBD_STATUS_DATA_BUFFER_ERROR       0xC0000013

#define USBD_STATUS_NOT_SUPPORTED           0xC0000E00
#define USBD_STATUS_BUFFER_TOO_SMALL        0xC0003000
#define USBD_STATUS_TIMEOUT                 0xC0006000
#define USBD_STATUS_DEVICE_GONE             0xC0007000

#define USBD_STATUS_NO_MEMORY               0x80000100
#define USBD_STATUS_INVALID_URB_FUNCTION    0x80000200
#define USBD_STATUS_INVALID_PARAMETER       0x80000300
#define USBD_STATUS_REQUEST_FAILED          0x80000500
#define USBD_STATUS_INVALID_PIPE_HANDLE     0x80000600
#define USBD_STATUS_ERROR_SHORT_TRANSFER    0x80000900

// Values for URB TransferFlags Field
//

/*
    Set if data moves device->host
*/
#define USBD_TRANSFER_DIRECTION               0x00000001
/*
    This bit if not set indicates that a short packet, and hence,
    a short transfer is an error condition
*/
#define USBD_SHORT_TRANSFER_OK                0x00000002
/*
    Subit the iso transfer on the next frame
*/
#define USBD_START_ISO_TRANSFER_ASAP          0x00000004
#define USBD_DEFAULT_PIPE_TRANSFER            0x00000008


#define USBD_TRANSFER_DIRECTION_FLAG(flags)  ((flags) & USBD_TRANSFER_DIRECTION)

#define USBD_TRANSFER_DIRECTION_OUT           0   
#define USBD_TRANSFER_DIRECTION_IN            1

#define VALID_TRANSFER_FLAGS_MASK             (USBD_SHORT_TRANSFER_OK | \
                                               USBD_TRANSFER_DIRECTION | \
                                               USBD_START_ISO_TRANSFER_ASAP | \
                                               USBD_DEFAULT_PIPE_TRANSFER)


 
 
#define ENDPOINT_HALT                   0x00  
#define DEVICE_REMOTE_WAKEUP            0x01  
 
 
/* transfer type */
#define CONTROL_TRANSFER         0x00
#define ISOCHRONOUS_TRANSFER     0x01    
#define BULK_TRANSFER            0x02  
#define INTERRUPT_TRANSFER       0x03



#define ClearHubFeature         (0x2000 | LIBUSB_REQUEST_CLEAR_FEATURE)
#define ClearPortFeature        (0x2300 | LIBUSB_REQUEST_CLEAR_FEATURE)
#define GetHubDescriptor        (0xa000 | LIBUSB_REQUEST_GET_DESCRIPTOR)
#define GetHubStatus            (0xa000 | LIBUSB_REQUEST_GET_STATUS)
#define GetPortStatus           (0xa300 | LIBUSB_REQUEST_GET_STATUS)
#define SetHubFeature           (0x2000 | LIBUSB_REQUEST_SET_FEATURE)
#define SetPortFeature          (0x2300 | LIBUSB_REQUEST_SET_FEATURE)



#define USBD_PF_CHANGE_MAX_PACKET         0x00000001
#define USBD_PF_SHORT_PACKET_OPT          0x00000002 
#define USBD_PF_ENABLE_RT_THREAD_ACCESS   0x00000004 
#define USBD_PF_MAP_ADD_TRANSFERS         0x00000008 

/* feature request */
#define URB_SET_FEATURE         0x00
#define URB_CLEAR_FEATURE       0x01

#define USBD_PF_CHANGE_MAX_PACKET         0x00000001
#define USBD_PF_SHORT_PACKET_OPT          0x00000002 
#define USBD_PF_ENABLE_RT_THREAD_ACCESS   0x00000004 
#define USBD_PF_MAP_ADD_TRANSFERS         0x00000008 


#define URB_CONTROL_TRANSFER_EXTERNAL       0x1
#define URB_CONTROL_TRANSFER_NONEXTERNAL    0x0


#define USBFS_URB_SHORT_NOT_OK      0x01
#define USBFS_URB_ISO_ASAP          0x02
#define USBFS_URB_BULK_CONTINUATION 0x04
#define USBFS_URB_QUEUE_BULK        0x10


#define URBDRC_DEVICE_INITIALIZED           0x01
#define URBDRC_DEVICE_NOT_FOUND             0x02
#define URBDRC_DEVICE_SIGNAL_END            0x04
#define URBDRC_DEVICE_CHANNEL_CLOSED        0x08
#define URBDRC_DEVICE_ALREADY_SEND          0x10
#define URBDRC_DEVICE_DETACH_KERNEL         0x20

#define MAX_URB_REQUSET_NUM  0x80


#define LOG_LEVEL 1
#define LLOG(_level, _args) \
  do { if (_level < LOG_LEVEL) { printf _args ; } } while (0)
#define LLOGLN(_level, _args) \
  do { if (_level < LOG_LEVEL) { printf _args ; printf("\n"); } } while (0)

  
#define dummy_wait_obj(void) do{ sleep(5); } while(0)  
#define dummy_wait_s_obj(_s) do{ sleep(_s); } while(0)  

#define ISOCH_FIFO              1
#define WAIT_COMPLETE_SLEEP     10000  /* for cpu high loading */

#define urbdrc_get_mstime(_t) do { \
	struct timeval _tp; \
	gettimeofday(&_tp, 0); \
	_t = (_tp.tv_sec * 1000) + (_tp.tv_usec / 1000); \
} while (0)  


extern int urbdrc_debug;

#endif /* __URBDRC_TYPES_H */
