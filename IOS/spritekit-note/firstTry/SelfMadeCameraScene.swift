//
//  SelfMadeCameraScene.swift
//  firstTry
//
//  Created by wanglulu on 15/12/6.
//  Copyright © 2015年 wanglulu. All rights reserved.
//
/****************************************************
本Demo显示了手动实现camera效果的代码

手动camera下，HUD的实现：

多层背景的实现：
    1.在scene中添加多个背景(而不是在world中)
    2.为多个每个背景设置不同的zPosition以分层
    3.zPosition越小的越远，其坐标移动幅度越小



重点: position与zPosition
1.  Sprite的zPosition决定了Sprite的前后关系，zPosition越大
    就越靠前，zPosition越小就越靠后。利用zPosition可实现Sprite的分层，
    sprite的position是相对父节点的，而zPosition却是绝对的，
    zPosition决定了Sprite的前后关系，这与添加到哪个节点无关。
2.  zPosition只决定了显示的先后顺序，而不能影响碰撞，即两物体即使
    zPosition不同相接处也会发生碰撞和接触事件。
*****************************************************/
import Foundation
import SpriteKit

class SelfMadeCameraScene:SKScene{
    
    let world = SKNode()
    let player = SKSpriteNode()
    
    override func didMoveToView(view: SKView) {
        self.size = CGSize(width: 900, height: 800)
        
        //world's position is not important, the func didSimulatePhysics:  will adjust
        //the world's position to make player at the center of the scene
        //world.position = CGPoint(x: self.size.width/2, y: self.size.height/2)
        //print(world.position)
        
        let background = SKSpriteNode(imageNamed:"background.png")
        background.position = CGPoint(x: 200 , y: 200)
        background.size = CGSize(width: 1130, height: 700)
        world.addChild(background)
        
        print("world"+"\(world.zPosition)")
        
        self.addChild(world)
        
        self.setPlayer()
    }
    
    func setPlayer()->(){
        
        //add player to world not self!!!
        world.addChild(player)
        
        player.size = CGSize(width: 105,height: 85)
        
        //player's position is not important it just define the player's position 
        //in the background but the screen, the func didSimulatePhysics: will adjust
        //the world's position to make player at the center of the scene
        //
        player.position = CGPointMake(400, 300)

        //使player位于background的上面，以免被background覆盖住。
        player.zPosition = 1;
        
        let birdAtlas = SKTextureAtlas(named: "fly.atlas")
        let birdFrame:[SKTexture] = [
            birdAtlas.textureNamed("fly1.png"),
            birdAtlas.textureNamed("fly2.png")]
        
        
        let fAction = SKAction.animateWithTextures(birdFrame, timePerFrame: 0.14)
        let flyAction = SKAction.repeatActionForever(fAction)
        player.runAction(flyAction)
        
        let leftPath = SKAction.moveByX(-200, y: -10, duration: 2)
        let rightPath = SKAction.moveByX(200, y: 10, duration: 2)
        let flipNegative = SKAction.scaleXTo(-1, duration: 0)
        let flipPositive = SKAction.scaleXTo(1, duration: 0)
        
        let move = SKAction.sequence([leftPath, flipNegative, rightPath, flipPositive])
        let alwaysMove = SKAction.repeatActionForever(move)
        
        player.runAction(alwaysMove)

    }
    
    override func didSimulatePhysics() {
        
        //该部分是核心，player显示的位置由world在场景中的position和player在world中的position决定
        //此外camera放大缩小效果可以通过改变场景大小或world的scale来实现
        let worldx = -(player.position.x*world.xScale - self.size.width/2)
        let worldy = -(player.position.y*world.yScale - self.size.height/2)
        
        world.position = CGPoint(x: worldx, y: worldy)
    }
    
}