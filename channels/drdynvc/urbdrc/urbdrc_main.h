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



#ifndef __URBDRC_MAIN_H
#define __URBDRC_MAIN_H

#include "searchman.h"
#include "isoch_queue.h"

#define DEVICE_HARDWARE_ID_SIZE             32
#define DEVICE_COMPATIBILITY_ID_SIZE        36
#define DEVICE_INSTANCE_STR_SIZE            37
#define DEVICE_CONTAINER_STR_SIZE           39


typedef struct _IUDEVICE IUDEVICE;
typedef struct _IUDEVMAN IUDEVMAN;

#define BASIC_DEV_STATE_DEFINED(_arg, _type) \
	_type (*get_##_arg) (IUDEVICE *pdev); \
	void (*set_##_arg) (IUDEVICE *pdev, _type _arg)
#define BASIC_DEVMAN_STATE_DEFINED(_arg, _type) \
	_type (*get_##_arg) (IUDEVMAN *udevman); \
	void (*set_##_arg) (IUDEVMAN *udevman, _type _arg)


typedef struct _URBDRC_LISTENER_CALLBACK URBDRC_LISTENER_CALLBACK;
struct _URBDRC_LISTENER_CALLBACK
{
	IWTSListenerCallback iface;

	IWTSPlugin * plugin;
	IWTSVirtualChannelManager * channel_mgr;
};

typedef struct _URBDRC_CHANNEL_CALLBACK URBDRC_CHANNEL_CALLBACK;
struct _URBDRC_CHANNEL_CALLBACK
{
	IWTSVirtualChannelCallback iface;

	IWTSPlugin * plugin;
	IWTSVirtualChannelManager * channel_mgr;
	IWTSVirtualChannel * channel;
};

typedef struct _URBDRC_PLUGIN URBDRC_PLUGIN;
struct _URBDRC_PLUGIN
{
	IWTSPlugin iface;

	URBDRC_LISTENER_CALLBACK * listener_callback;

	IUDEVMAN * udevman;
	USB_SEARCHMAN * searchman;
	uint32 first_channel_id;
	uint32 vchannel_status;
};


#define URBDRC_UDEVMAN_EXPORT_FUNC_NAME "FreeRDPUDEVMANEntry"

typedef void (*PREGISTERURBDRCSERVICE)(IWTSPlugin* plugin, IUDEVMAN* udevman);

struct _FREERDP_URBDRC_SERVICE_ENTRY_POINTS
{
	IWTSPlugin* plugin;
	PREGISTERURBDRCSERVICE pRegisterUDEVMAN;
	RDP_PLUGIN_DATA* plugin_data;
};
typedef struct _FREERDP_URBDRC_SERVICE_ENTRY_POINTS FREERDP_URBDRC_SERVICE_ENTRY_POINTS;
typedef FREERDP_URBDRC_SERVICE_ENTRY_POINTS* PFREERDP_URBDRC_SERVICE_ENTRY_POINTS;

typedef int (*PFREERDP_URBDRC_DEVICE_ENTRY)(PFREERDP_URBDRC_SERVICE_ENTRY_POINTS pEntryPoints);




typedef struct _TRANSFER_DATA TRANSFER_DATA;
struct _TRANSFER_DATA
{
	URBDRC_CHANNEL_CALLBACK * callback;
	URBDRC_PLUGIN * urbdrc;
	IUDEVMAN *  udevman;
	uint8 *     pBuffer;
	uint32      cbSize;
	uint32      UsbDevice;
};


struct _IUDEVICE
{
	/* Transfer */
	int (*isoch_transfer) (IUDEVICE * idev, uint32 RequestId,
	                                            uint32 EndpointAddress,
	                                            uint32 TransferFlags,
	                                            int NoAck,
	                                            uint32 *ErrorCount,
	                                            uint32 *UrbdStatus,
	                                            uint32 *StartFrame,
	                                            uint32 NumberOfPackets,
	                                            uint8 *IsoPacket,
	                                            uint32 *BufferSize,
	                                            uint8 *Buffer,
	                                            int Timeout);

	int (*control_transfer) (IUDEVICE * idev, uint32 RequestId,
	                                            uint32 EndpointAddress,
	                                            uint32 TransferFlags,
	                                            uint8 bmRequestType,
	                                            uint8 Request,
	                                            uint16 Value,
	                                            uint16 Index,
	                                            uint32 *UrbdStatus,
	                                            uint32 *BufferSize,
	                                            uint8 *Buffer,
	                                            uint32 Timeout);

	int (*bulk_or_interrupt_transfer) (IUDEVICE * idev, uint32 RequestId,
	                                            uint32 EndpointAddress,
	                                            uint32 TransferFlags,
	                                            uint32 *UsbdStatus,
	                                            uint32 *BufferSize,
	                                            uint8 *Buffer,
	                                            uint32 Timeout);


	int (*select_configuration) (IUDEVICE * idev, uint32 bConfigurationValue);

	int (*select_interface) (IUDEVICE * idev, uint8 InterfaceNumber,
	                                            uint8 AlternateSetting);

	int (*control_pipe_request) (IUDEVICE * idev, uint32 RequestId,
	                                            uint32 EndpointAddress,
	                                            uint32 *UsbdStatus,
	                                            int command);

	int (*control_query_device_text) (IUDEVICE * idev, uint32 TextType,
	                                            uint32 LocaleId,
	                                            uint32 *BufferSize,
	                                            uint8 * Buffer);

	int (*os_feature_descriptor_request) (IUDEVICE * idev, uint32 RequestId,
	                                            uint8 Recipient,
	                                            uint8 InterfaceNumber,
	                                            uint8 Ms_PageIndex,
	                                            uint16 Ms_featureDescIndex,
	                                            uint32 * UsbdStatus,
	                                            uint32 * BufferSize,
	                                            uint8* Buffer,
	                                            int Timeout);

	void (*cancel_all_transfer_request) (IUDEVICE * idev);

	int (*cancel_transfer_request) (IUDEVICE * idev, uint32 RequestId);

	int (*query_device_descriptor) (IUDEVICE * idev, int offset);

	void (*detach_kernel_driver) (IUDEVICE * idev);

	void (*attach_kernel_driver) (IUDEVICE * idev);

	int (*wait_action_completion) (IUDEVICE * idev);

	void (*push_action) (IUDEVICE * idev);

	void (*complete_action) (IUDEVICE * idev);

	/* Wait for 5 sec */
	int (*wait_for_detach) (IUDEVICE * idev);

	/* FIXME: Currently this is a way of stupid, SHOULD to improve it.
	 *        Isochronous transfer must to FIFO */
	void (*lock_fifo_isoch) (IUDEVICE * idev);
	void (*unlock_fifo_isoch) (IUDEVICE * idev);

	int (*query_device_port_status) (IUDEVICE * idev, uint32 *UsbdStatus,
	                                            uint32 * BufferSize,
	                                            uint8 * Buffer);

	int (*request_queue_is_none) (IUDEVICE * idev);

	MSUSB_CONFIG_DESCRIPTOR * (*complete_msconfig_setup) (IUDEVICE * idev,
	                                MSUSB_CONFIG_DESCRIPTOR * MsConfig);
	/* Basic state */
	int (*isCompositeDevice) (IUDEVICE * idev);
	int (*isSigToEnd) (IUDEVICE * idev);
	int (*isExist) (IUDEVICE * idev);
	int (*isAlreadySend) (IUDEVICE * idev);
	int (*isChannelClosed) (IUDEVICE * idev);
	void (*SigToEnd) (IUDEVICE * idev);
	void (*setAlreadySend) (IUDEVICE * idev);
	void (*setChannelClosed) (IUDEVICE * idev);

	BASIC_DEV_STATE_DEFINED(channel_id, uint32);
	BASIC_DEV_STATE_DEFINED(UsbDevice, uint32);
	BASIC_DEV_STATE_DEFINED(ReqCompletion, uint32);
	BASIC_DEV_STATE_DEFINED(bus_number, uint16);
	BASIC_DEV_STATE_DEFINED(dev_number, uint16);
	BASIC_DEV_STATE_DEFINED(port_number, int);
	BASIC_DEV_STATE_DEFINED(isoch_queue, void *);
	BASIC_DEV_STATE_DEFINED(MsConfig, MSUSB_CONFIG_DESCRIPTOR *);

	BASIC_DEV_STATE_DEFINED(p_udev, void *);
	BASIC_DEV_STATE_DEFINED(p_prev, void *);
	BASIC_DEV_STATE_DEFINED(p_next, void *);

	/* Control semaphore or mutex lock */

};



struct _IUDEVMAN
{
	/* Standard */
	void (*free) (IUDEVMAN *idevman);
	/* Manage devices */
	void (*rewind) (IUDEVMAN *idevman);
	int  (*has_next) (IUDEVMAN *idevman);
	int  (*unregister_udevice) (IUDEVMAN* idevman, int bus_number, int dev_number);
	int  (*register_udevice) (IUDEVMAN* idevman, int bus_number, int dev_number,
			int UsbDevice, uint16 idVendor, uint16 idProduct, char * option);
	IUDEVICE *(*get_next) (IUDEVMAN *idevman);
	IUDEVICE *(*get_udevice_by_UsbDevice) (IUDEVMAN * idevman, uint32 UsbDevice);
	IUDEVICE *(*get_udevice_by_UsbDevice_try_again) (IUDEVMAN * idevman, uint32 UsbDevice);
	/* Extension */
	int (*check_device_exist_by_id) (IUDEVMAN * idevman, uint16 idVendor, uint16 idProduct);
	/* Basic state */
	BASIC_DEVMAN_STATE_DEFINED(first_channel_id, uint32);
	BASIC_DEVMAN_STATE_DEFINED(defUsbDevice, uint32);
	BASIC_DEVMAN_STATE_DEFINED(device_num, int);
	BASIC_DEVMAN_STATE_DEFINED(sem_timeout, int);
	/* control semaphore or mutex lock */
	void (*loading_lock) (IUDEVMAN * idevman);
	void (*loading_unlock) (IUDEVMAN * idevman);
	void (*push_urb) (IUDEVMAN * idevman);
	void (*wait_urb) (IUDEVMAN * idevman);
};


#endif /* __URBDRC_MAIN_H */
